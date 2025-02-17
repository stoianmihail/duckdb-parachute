#include "duckdb/optimizer/join_order/relation_statistics_helper.hpp"
#include "duckdb/planner/expression/list.hpp"
#include "duckdb/planner/operator/list.hpp"
#include "duckdb/planner/filter/conjunction_filter.hpp"
#include "duckdb/planner/expression_iterator.hpp"
#include "duckdb/catalog/catalog_entry/table_catalog_entry.hpp"
#include "duckdb/function/table/table_scan.hpp"
#include "duckdb/planner/operator/logical_get.hpp"
#include "duckdb/storage/data_table.hpp"
#include "duckdb/planner/filter/constant_filter.hpp"

namespace duckdb {

static ExpressionBinding GetChildColumnBinding(Expression &expr) {
	auto ret = ExpressionBinding();
	switch (expr.GetExpressionClass()) {
	case ExpressionClass::BOUND_FUNCTION: {
		// TODO: Other expression classes that can have 0 children?
		auto &func = expr.Cast<BoundFunctionExpression>();
		// no children some sort of gen_random_uuid() or equivalent.
		if (func.children.empty()) {
			ret.found_expression = true;
			ret.expression_is_constant = true;
			return ret;
		}
		break;
	}
	case ExpressionClass::BOUND_COLUMN_REF: {
		ret.found_expression = true;
		auto &new_col_ref = expr.Cast<BoundColumnRefExpression>();
		ret.child_binding = ColumnBinding(new_col_ref.binding.table_index, new_col_ref.binding.column_index);
		return ret;
	}
	case ExpressionClass::BOUND_LAMBDA_REF:
	case ExpressionClass::BOUND_CONSTANT:
	case ExpressionClass::BOUND_DEFAULT:
	case ExpressionClass::BOUND_PARAMETER:
	case ExpressionClass::BOUND_REF:
		ret.found_expression = true;
		ret.expression_is_constant = true;
		return ret;
	default:
		break;
	}
	ExpressionIterator::EnumerateChildren(expr, [&](unique_ptr<Expression> &child) {
		auto recursive_result = GetChildColumnBinding(*child);
		if (recursive_result.found_expression) {
			ret = recursive_result;
		}
	});
	// we didn't find a Bound Column Ref
	return ret;
}

bool starts_with(std::string text, std::string pattern) {
	int text_len = text.size();
	int pattern_len = pattern.size();
	if (text_len < pattern_len) return false;
	return text.compare(0, pattern_len, pattern) == 0;
}

RelationStats RelationStatisticsHelper::ExtractGetStats(LogicalGet &get, ClientContext &context) {
	auto return_stats = RelationStats();

	auto base_table_cardinality = get.EstimateCardinality(context);
	auto cardinality_after_filters = base_table_cardinality;
	unique_ptr<BaseStatistics> column_statistics;

	auto catalog_table = get.GetTable();
	auto name = string("some table");
	if (catalog_table) {
		name = catalog_table->name;
		return_stats.table_name = name;
	}

	// if we can get the catalog table, then our column statistics will be accurate
	// parquet readers etc. will still return statistics, but they initialize distinct column
	// counts to 0.
	// TODO: fix this, some file formats can encode distinct counts, we don't want to rely on
	//  getting a catalog table to know that we can use statistics.
	bool have_catalog_table_statistics = false;
	if (get.GetTable()) {
		have_catalog_table_statistics = true;
	}

	// first push back basic distinct counts for each column (if we have them).
	auto &column_ids = get.GetColumnIds();
	for (idx_t i = 0; i < column_ids.size(); i++) {
		auto column_id = column_ids[i].GetPrimaryIndex();
		bool have_distinct_count_stats = false;

		// Skip if parachute column (and if `column_id` is valid, of course).
		if ((column_id < get.names.size()) && (starts_with(get.names.at(column_id), "parachute_"))) {
			continue;
		}

		if (get.function.statistics) {
			column_statistics = get.function.statistics(context, get.bind_data.get(), column_id);
			if (column_statistics && have_catalog_table_statistics) {
				auto distinct_count = MaxValue<idx_t>(1, column_statistics->GetDistinctCount());
				auto column_distinct_count = DistinctCount({distinct_count, true});
				return_stats.column_distinct_count.push_back(column_distinct_count);
				return_stats.column_names.push_back(name + "." + get.names.at(column_id));
				have_distinct_count_stats = true;
			}
		}
		if (!have_distinct_count_stats) {
			// currently treating the cardinality as the distinct count.
			// the cardinality estimator will update these distinct counts based
			// on the extra columns that are joined on.
			auto column_distinct_count = DistinctCount({cardinality_after_filters, false});
			return_stats.column_distinct_count.push_back(column_distinct_count);
			auto column_name = string("column");
			if (column_id < get.names.size()) {
				column_name = get.names.at(column_id);
			}
			return_stats.column_names.push_back(get.GetName() + "." + column_name);
		}
	}

	std::string table_name = "dummy_table";
	if (get.GetTable()) {
		table_name = get.GetTable()->name;
	}
	
	auto parachute_stats_file = ClientConfig::GetSetting<ParachuteStatsSetting>(context);
	auto parachute_stats = ClientConfig::GetConfig(context).GetParachuteStats();
	bool use_parachute_stats = (!parachute_stats_file.empty());
	unsigned parachute_filter_count = 0;

	// std::cerr << "\ntable_name=" << table_name << std::endl;

	if (!get.table_filters.filters.empty()) {
		bool has_supported_filter = false;
		column_statistics = nullptr;
		bool has_non_optional_filters = false;
		for (auto &it : get.table_filters.filters) {
			if (get.bind_data && get.function.statistics) {
				column_statistics = get.function.statistics(context, get.bind_data.get(), it.first);
			}

			// NOTE: There are two options.
			// NOTE: We can either estimate before, during or after.
			// NOTE: Before: Estimate the table size first with parachutes.
			// NOTE: During: With the actual filters (more natural).
			// NOTE: After: After the actual filters have been applied.
			// NOTE: We can have a mode=-1, 0, 1, 2.

			// Take the column name.
			std::string column_name = "dummy_column";
			if (get.GetTable()) {
				column_name = get.GetTable()->GetColumn(LogicalIndex(it.first)).Name();
			}
			auto is_parachute_col = starts_with(column_name, "parachute_");

			// std::cerr << "--- column_name=" << column_name << std::endl;

			if (column_statistics) {
				idx_t cardinality_with_filter = cardinality_after_filters;
				if (is_parachute_col) {
					if (use_parachute_stats) {
						cardinality_with_filter = InspectParachuteFilter(parachute_stats, base_table_cardinality, it.first, *it.second, table_name, column_name, *column_statistics);
					} else {
						// Don't even try to estimate.
					}

					// Still increase the number of parachute filters.
					++parachute_filter_count;
				} else {
					cardinality_with_filter = InspectTableFilter(base_table_cardinality, it.first, *it.second, *column_statistics, has_supported_filter);
				}
				cardinality_after_filters = MinValue(cardinality_after_filters, cardinality_with_filter);
			}

			if (it.second->filter_type != TableFilterType::OPTIONAL_FILTER) {
				if (is_parachute_col) {
					// TODO
				} else {
					has_non_optional_filters = true;	
				}
			}
		}

		// std::cerr << "has_supported_filter=" << has_supported_filter << " has_non_optional_filter=" << has_non_optional_filters << std::endl;
		// std::cerr << "parachute_filter_count=" << parachute_filter_count << " filters.size()=" << get.table_filters.filters.size() << std::endl;

		// if the above code didn't find an equality filter (i.e country_code = "[us]")
		// and there are other table filters (i.e cost > 50), use default selectivity.
		// TODO: This is wrong in DuckDB v1.2.0, since the cardinality _can_ still be the base one.
		bool has_equality_filter = (cardinality_after_filters != base_table_cardinality);
		if ((!use_parachute_stats) && (!parachute_filter_count)) {
			if ((!has_equality_filter) && (has_non_optional_filters)) {
				// DuckDB v1.2.0.
				cardinality_after_filters = MaxValue<idx_t>(LossyNumericCast<idx_t>(double(base_table_cardinality) * RelationStatisticsHelper::DEFAULT_SELECTIVITY), 1U);
			}
		} else if ((!use_parachute_stats) && (parachute_filter_count)) {
			if (parachute_filter_count == get.table_filters.filters.size()) {
				// noop.
			} else {
				if ((!has_equality_filter) && (has_non_optional_filters)) {
					// DuckDB v1.2.0.
					cardinality_after_filters = MaxValue<idx_t>(LossyNumericCast<idx_t>(double(base_table_cardinality) * RelationStatisticsHelper::DEFAULT_SELECTIVITY), 1U);
				}
			}
		} else {
			// TODO.
			assert(0);
		}

		if (base_table_cardinality == 0) {
			cardinality_after_filters = 0;
		}
	}
	return_stats.cardinality = cardinality_after_filters;
	// update the estimated cardinality of the get as well.
	// This is not updated during plan reconstruction.
	get.estimated_cardinality = cardinality_after_filters;
	get.has_estimated_cardinality = true;
	D_ASSERT(base_table_cardinality >= cardinality_after_filters);
	return_stats.stats_initialized = true;
	return return_stats;
}

RelationStats RelationStatisticsHelper::ExtractDelimGetStats(LogicalDelimGet &delim_get, ClientContext &context) {
	RelationStats stats;
	stats.table_name = delim_get.GetName();
	idx_t card = delim_get.EstimateCardinality(context);
	stats.cardinality = card;
	stats.stats_initialized = true;
	for (auto &binding : delim_get.GetColumnBindings()) {
		stats.column_distinct_count.push_back(DistinctCount({1, false}));
		stats.column_names.push_back("column" + to_string(binding.column_index));
	}
	return stats;
}

RelationStats RelationStatisticsHelper::ExtractProjectionStats(LogicalProjection &proj, RelationStats &child_stats) {
	auto proj_stats = RelationStats();
	proj_stats.cardinality = child_stats.cardinality;
	proj_stats.table_name = proj.GetName();
	for (auto &expr : proj.expressions) {
		proj_stats.column_names.push_back(expr->GetName());
		auto res = GetChildColumnBinding(*expr);
		D_ASSERT(res.found_expression);
		if (res.expression_is_constant) {
			proj_stats.column_distinct_count.push_back(DistinctCount({1, true}));
		} else {
			auto column_index = res.child_binding.column_index;
			if (column_index >= child_stats.column_distinct_count.size() && expr->ToString() == "count_star()") {
				// only one value for a count star
				proj_stats.column_distinct_count.push_back(DistinctCount({1, true}));
			} else {
				// TODO: add this back in
				//	D_ASSERT(column_index < stats.column_distinct_count.size());
				if (column_index < child_stats.column_distinct_count.size()) {
					proj_stats.column_distinct_count.push_back(child_stats.column_distinct_count.at(column_index));
				} else {
					proj_stats.column_distinct_count.push_back(DistinctCount({proj_stats.cardinality, false}));
				}
			}
		}
	}
	proj_stats.stats_initialized = true;
	return proj_stats;
}

RelationStats RelationStatisticsHelper::ExtractDummyScanStats(LogicalDummyScan &dummy_scan, ClientContext &context) {
	auto stats = RelationStats();
	idx_t card = dummy_scan.EstimateCardinality(context);
	stats.cardinality = card;
	for (idx_t i = 0; i < dummy_scan.GetColumnBindings().size(); i++) {
		stats.column_distinct_count.push_back(DistinctCount({card, false}));
		stats.column_names.push_back("dummy_scan_column");
	}
	stats.stats_initialized = true;
	stats.table_name = "dummy scan";
	return stats;
}

void RelationStatisticsHelper::CopyRelationStats(RelationStats &to, const RelationStats &from) {
	to.column_distinct_count = from.column_distinct_count;
	to.column_names = from.column_names;
	to.cardinality = from.cardinality;
	to.table_name = from.table_name;
	to.stats_initialized = from.stats_initialized;
}

RelationStats RelationStatisticsHelper::CombineStatsOfReorderableOperator(vector<ColumnBinding> &bindings,
                                                                          vector<RelationStats> relation_stats) {
	RelationStats stats;
	idx_t max_card = 0;
	for (auto &child_stats : relation_stats) {
		for (idx_t i = 0; i < child_stats.column_distinct_count.size(); i++) {
			stats.column_distinct_count.push_back(child_stats.column_distinct_count.at(i));
			stats.column_names.push_back(child_stats.column_names.at(i));
		}
		stats.table_name += "joined with " + child_stats.table_name;
		max_card = MaxValue(max_card, child_stats.cardinality);
	}
	stats.stats_initialized = true;
	stats.cardinality = max_card;
	return stats;
}

RelationStats RelationStatisticsHelper::CombineStatsOfNonReorderableOperator(LogicalOperator &op,
                                                                             vector<RelationStats> child_stats) {
	D_ASSERT(child_stats.size() == 2);
	RelationStats ret;
	idx_t child_1_card = child_stats[0].stats_initialized ? child_stats[0].cardinality : 0;
	idx_t child_2_card = child_stats[1].stats_initialized ? child_stats[1].cardinality : 0;
	ret.cardinality = MaxValue(child_1_card, child_2_card);
	switch (op.type) {
	case LogicalOperatorType::LOGICAL_COMPARISON_JOIN: {
		auto &join = op.Cast<LogicalComparisonJoin>();
		switch (join.join_type) {
		case JoinType::RIGHT_ANTI:
		case JoinType::RIGHT_SEMI:
			ret.cardinality = child_2_card;
			break;
		case JoinType::ANTI:
		case JoinType::SEMI:
		case JoinType::SINGLE:
		case JoinType::MARK:
			ret.cardinality = child_1_card;
			break;
		default:
			break;
		}
		break;
	}
	case LogicalOperatorType::LOGICAL_UNION: {
		auto &setop = op.Cast<LogicalSetOperation>();
		if (setop.setop_all) {
			// setop returns all records
			ret.cardinality = child_1_card + child_2_card;
		} else {
			ret.cardinality = MaxValue(child_1_card, child_2_card);
		}
		break;
	}
	case LogicalOperatorType::LOGICAL_INTERSECT: {
		ret.cardinality = MinValue(child_1_card, child_2_card);
		break;
	}
	case LogicalOperatorType::LOGICAL_EXCEPT: {
		ret.cardinality = child_1_card;
		break;
	}
	default:
		break;
	}

	ret.stats_initialized = true;
	ret.filter_strength = 1;
	ret.table_name = child_stats[0].table_name + " joined with " + child_stats[1].table_name;
	for (auto &stats : child_stats) {
		// MARK joins are nonreorderable. They won't return initialized stats
		// continue in this case.
		if (!stats.stats_initialized) {
			continue;
		}
		for (auto &distinct_count : stats.column_distinct_count) {
			ret.column_distinct_count.push_back(distinct_count);
		}
		for (auto &column_name : stats.column_names) {
			ret.column_names.push_back(column_name);
		}
	}
	return ret;
}

RelationStats RelationStatisticsHelper::ExtractExpressionGetStats(LogicalExpressionGet &expression_get,
                                                                  ClientContext &context) {
	auto stats = RelationStats();
	idx_t card = expression_get.EstimateCardinality(context);
	stats.cardinality = card;
	for (idx_t i = 0; i < expression_get.GetColumnBindings().size(); i++) {
		stats.column_distinct_count.push_back(DistinctCount({card, false}));
		stats.column_names.push_back("expression_get_column");
	}
	stats.stats_initialized = true;
	stats.table_name = "expression_get";
	return stats;
}

RelationStats RelationStatisticsHelper::ExtractWindowStats(LogicalWindow &window, RelationStats &child_stats) {
	RelationStats stats;
	stats.cardinality = child_stats.cardinality;
	stats.column_distinct_count = child_stats.column_distinct_count;
	stats.column_names = child_stats.column_names;
	stats.stats_initialized = true;
	auto num_child_columns = window.GetColumnBindings().size();

	for (idx_t column_index = child_stats.column_distinct_count.size(); column_index < num_child_columns;
	     column_index++) {
		stats.column_distinct_count.push_back(DistinctCount({child_stats.cardinality, false}));
		stats.column_names.push_back("window");
	}
	return stats;
}

RelationStats RelationStatisticsHelper::ExtractAggregationStats(LogicalAggregate &aggr, RelationStats &child_stats) {
	RelationStats stats;
	// TODO: look at child distinct count to better estimate cardinality.
	stats.cardinality = child_stats.cardinality;
	stats.column_distinct_count = child_stats.column_distinct_count;
	double new_card = -1;
	for (auto &g_set : aggr.grouping_sets) {
		for (auto &ind : g_set) {
			if (aggr.groups[ind]->GetExpressionClass() != ExpressionClass::BOUND_COLUMN_REF) {
				continue;
			}
			auto bound_col = &aggr.groups[ind]->Cast<BoundColumnRefExpression>();
			auto col_index = bound_col->binding.column_index;
			if (col_index >= child_stats.column_distinct_count.size()) {
				// it is possible the column index of the grouping_set is not in the child stats.
				// this can happen when delim joins are present, since delim scans are not currently
				// reorderable. Meaning they don't add a relation or column_ids that could potentially
				// be grouped by. Hopefully this can be fixed with duckdb-internal#606
				continue;
			}
			double distinct_count = double(child_stats.column_distinct_count[col_index].distinct_count);
			if (new_card < distinct_count) {
				new_card = distinct_count;
			}
		}
	}
	if (new_card < 0 || new_card >= double(child_stats.cardinality)) {
		// We have no good statistics on distinct count.
		// most likely we are running on parquet files. Therefore we divide by 2.
		new_card = (double)child_stats.cardinality / 2;
	}
	// an ungrouped aggregate has 1 row
	stats.cardinality = aggr.groups.empty() ? 1 : LossyNumericCast<idx_t>(new_card);
	stats.column_names = child_stats.column_names;
	stats.stats_initialized = true;
	auto num_child_columns = aggr.GetColumnBindings().size();

	for (idx_t column_index = child_stats.column_distinct_count.size(); column_index < num_child_columns;
	     column_index++) {
		stats.column_distinct_count.push_back(DistinctCount({child_stats.cardinality, false}));
		stats.column_names.push_back("aggregate");
	}
	return stats;
}

RelationStats RelationStatisticsHelper::ExtractEmptyResultStats(LogicalEmptyResult &empty) {
	RelationStats stats;
	for (idx_t i = 0; i < empty.GetColumnBindings().size(); i++) {
		stats.column_distinct_count.push_back(DistinctCount({0, false}));
		stats.column_names.push_back("empty_result_column");
	}
	stats.stats_initialized = true;
	return stats;
}


std::string TableFilterTypeToString(TableFilterType type) {
	switch (type) {
		case TableFilterType::CONSTANT_COMPARISON: return "CONSTANT_COMPARISON";
		case TableFilterType::IS_NULL: return "IS_NULL";
		case TableFilterType::IS_NOT_NULL: return "IS_NOT_NULL";
		case TableFilterType::CONJUNCTION_OR: return "CONJUNCTION_OR";
		case TableFilterType::CONJUNCTION_AND: return "CONJUNCTION_AND";
		case TableFilterType::STRUCT_EXTRACT: return "STRUCT_EXTRACT";
		case TableFilterType::OPTIONAL_FILTER: return "OPTIONAL_FILTER";
		case TableFilterType::IN_FILTER: return "IN_FILTER";
		case TableFilterType::DYNAMIC_FILTER: return "DYNAMIC_FILTER";
		default: return "UNKNOWN";
	}
}

idx_t RelationStatisticsHelper::InspectParachuteFilter(ParachuteStats& stats, idx_t cardinality, idx_t column_index,  TableFilter &filter, std::string tab_name, std::string col_name, BaseStatistics &base_stats) {
	auto cardinality_after_filters = cardinality;
	
	// std::cerr << "[InspectParachuteFilter] tn=" << tab_name << " cn=" << col_name << std::endl;

	std::cerr << "filter_type=" << TableFilterTypeToString(filter.filter_type) << std::endl;

	switch (filter.filter_type) {
		case TableFilterType::CONJUNCTION_AND: {
			// NOTE: Should never come into here!
			assert(0);
			// auto &and_filter = filter.Cast<ConjunctionAndFilter>();
			// for (auto &child_filter : and_filter.child_filters) {
			// 	cardinality_after_filters = MinValue(
			// 			cardinality_after_filters, InspectTableFilter(cardinality, column_index, *child_filter, base_stats));
			// }
			// return cardinality_after_filters;
		}
		case TableFilterType::CONSTANT_COMPARISON: {
			auto &comparison_filter = filter.Cast<ConstantFilter>();
			switch (comparison_filter.comparison_type) {
				case ExpressionType::COMPARE_EQUAL: {
					// std::cerr << "filter =" << std::endl;
					auto val = comparison_filter.constant.GetValue<uint32_t>();

					// std::cerr << "tab_name=" << tab_name << " col_name=" << col_name << std::endl;

					// TODO: Don't return if we have multiple filters (later).
					if (!stats.has(tab_name, col_name))
						return cardinality_after_filters;

					auto sel = stats.compute_selectivity(tab_name, col_name, "=", val);

					// std::cerr << "[" << col_name << " = " << val << "]: sel=" << sel << std::endl;

					return static_cast<idx_t>(sel * cardinality_after_filters);
				}
				case ExpressionType::COMPARE_LESSTHAN: {
					auto val = comparison_filter.constant.GetValue<uint32_t>();

					// TODO: Don't return if we have multiple filters (later).
					if (!stats.has(tab_name, col_name))
						return cardinality_after_filters;

					auto sel = stats.compute_selectivity(tab_name, col_name, "<", val);

					// std::cerr << "[" << col_name << " < " << val << "]: sel=" << sel << std::endl;

					return static_cast<idx_t>(sel * cardinality_after_filters);
				}
				case ExpressionType::COMPARE_LESSTHANOREQUALTO: {
					auto val = comparison_filter.constant.GetValue<uint32_t>();

					// TODO: Don't return if we have multiple filters (later).
					if (!stats.has(tab_name, col_name))
						return cardinality_after_filters;

					auto sel = stats.compute_selectivity(tab_name, col_name, "<=", val);

					// std::cerr << "[" << col_name << " <= " << val << "]: sel=" << sel << std::endl;

					return static_cast<idx_t>(sel * cardinality_after_filters);
				}
				case ExpressionType::COMPARE_GREATERTHAN: {
					auto val = comparison_filter.constant.GetValue<uint32_t>();

					// TODO: Don't return if we have multiple filters (later).
					if (!stats.has(tab_name, col_name))
						return cardinality_after_filters;

					auto sel = stats.compute_selectivity(tab_name, col_name, ">", val);

					// std::cerr << "[" << col_name << " > " << val << "]: sel=" << sel << std::endl;

					return static_cast<idx_t>(sel * cardinality_after_filters);
				}
				case ExpressionType::COMPARE_GREATERTHANOREQUALTO: {
					auto val = comparison_filter.constant.GetValue<uint32_t>();

					// TODO: Don't return if we have multiple filters (later).
					if (!stats.has(tab_name, col_name))
						return cardinality_after_filters;

					auto sel = stats.compute_selectivity(tab_name, col_name, ">=", val);

					// std::cerr << "[" << col_name << " >= " << val << "]: sel=" << sel << std::endl;

					return static_cast<idx_t>(sel * cardinality_after_filters);
				}
				case ExpressionType::COMPARE_BETWEEN: {
					std::cerr << "between!" << std::endl;
					// auto &between = filter.Cast<BoundBetweenExpression>();
					// assert(between.lower->GetExpressionType() == ExpressionType::VALUE_CONSTANT);
					// assert(between.upper->GetExpressionType() == ExpressionType::VALUE_CONSTANT);

					// auto lb = between.lower->Cast<BoundConstantExpression>().value;
					// // low_value = between.lower->Cast<BoundConstantExpression>().value;
					// // low_comparison_type = between.lower_inclusive ? ExpressionType::COMPARE_GREATERTHANOREQUALTO : ExpressionType::COMPARE_GREATERTHAN;
					// auto ub = (between.upper->Cast<BoundConstantExpression>()).value;
					// // high_comparison_type = between.upper_inclusive ? ExpressionType::COMPARE_LESSTHANOREQUALTO : ExpressionType::COMPARE_LESSTHAN;

					// std::cerr << "lb=" << lb << " ub=" << ub << std::endl;

					// if (!stats.has(tab_name, col_name))
					// 	return cardinality_after_filters;


					auto sel = 0.2;//stats.compute_selectivity(tab_name, col_name, ">=", val);

					// std::cerr << "[" << col_name << " >= " << val << "]: sel=" << sel << std::endl;

					return static_cast<idx_t>(sel * cardinality_after_filters);
					// auto sel = stats.compute_selectivity(tab_name, col_name, 'between', low_value, high_value);
				}
				default: {
					std::cerr << "here!" << std::endl;
					assert(0);
					return cardinality_after_filters;
				}
			}
		}
		default: {
			std::cerr << "or here????" << std::endl;
			assert(0);
			return cardinality_after_filters;
		}
	}

	// Unreachable.
	assert(0);
}

idx_t RelationStatisticsHelper::InspectTableFilter(idx_t cardinality, idx_t column_index, TableFilter &filter,
                                                   BaseStatistics &base_stats, bool &has_supported_filter) {
	auto cardinality_after_filters = cardinality;
	switch (filter.filter_type) {
	case TableFilterType::CONJUNCTION_AND: {
		auto &and_filter = filter.Cast<ConjunctionAndFilter>();
		for (auto &child_filter : and_filter.child_filters) {
			cardinality_after_filters = MinValue(
			    cardinality_after_filters, InspectTableFilter(cardinality, column_index, *child_filter, base_stats, has_supported_filter));
		}
		return cardinality_after_filters;
	}
	case TableFilterType::CONSTANT_COMPARISON: {
		auto &comparison_filter = filter.Cast<ConstantFilter>();
		if (comparison_filter.comparison_type != ExpressionType::COMPARE_EQUAL) {
			return cardinality_after_filters;
		}

		// Mark as supported.
		has_supported_filter = true;

		auto column_count = base_stats.GetDistinctCount();
		// column_count = 0 when there is no column count (i.e parquet scans)
		if (column_count > 0) {
			// we want the ceil of cardinality/column_count. We also want to avoid compiler errors
			cardinality_after_filters = (cardinality + column_count - 1) / column_count;
		}
		// TODO: Shouldn't here be zero?
		return cardinality_after_filters;
	}
	default:
		return cardinality_after_filters;
	}
}

// TODO: Currently only simple AND filters are pushed into table scans.
//  When OR filters are pushed this function can be added
// idx_t RelationStatisticsHelper::InspectConjunctionOR(idx_t cardinality, idx_t column_index, ConjunctionOrFilter
// &filter,
//                                                     BaseStatistics &base_stats) {
//	auto has_equality_filter = false;
//	auto cardinality_after_filters = cardinality;
//	for (auto &child_filter : filter.child_filters) {
//		if (child_filter->filter_type != TableFilterType::CONSTANT_COMPARISON) {
//			continue;
//		}
//		auto &comparison_filter = child_filter->Cast<ConstantFilter>();
//		if (comparison_filter.comparison_type == ExpressionType::COMPARE_EQUAL) {
//			auto column_count = base_stats.GetDistinctCount();
//			auto increment = MaxValue<idx_t>(((cardinality + column_count - 1) / column_count), 1);
//			if (has_equality_filter) {
//				cardinality_after_filters += increment;
//			} else {
//				cardinality_after_filters = increment;
//			}
//			has_equality_filter = true;
//		}
//		if (child_filter->filter_type == TableFilterType::CONJUNCTION_AND) {
//			auto &and_filter = child_filter->Cast<ConjunctionAndFilter>();
//			cardinality_after_filters = RelationStatisticsHelper::InspectConjunctionAND(
//			    cardinality_after_filters, column_index, and_filter, base_stats);
//			continue;
//		}
//	}
//	D_ASSERT(cardinality_after_filters > 0);
//	return cardinality_after_filters;
//}

} // namespace duckdb