/*
 * Copyright Elasticsearch B.V. and/or licensed to Elasticsearch B.V. under one
 * or more contributor license agreements. Licensed under the Elastic License
 * 2.0; you may not use this file except in compliance with the Elastic License
 * 2.0.
 */

package org.elasticsearch.xpack.esql.optimizer.rules.logical.promql;

import org.elasticsearch.xpack.esql.core.expression.Alias;
import org.elasticsearch.xpack.esql.core.expression.Attribute;
import org.elasticsearch.xpack.esql.core.expression.Expression;
import org.elasticsearch.xpack.esql.core.expression.FieldAttribute;
import org.elasticsearch.xpack.esql.core.expression.Literal;
import org.elasticsearch.xpack.esql.core.expression.MetadataAttribute;
import org.elasticsearch.xpack.esql.core.expression.ReferenceAttribute;
import org.elasticsearch.xpack.esql.core.expression.TimeSeriesMetadataAttribute;
import org.elasticsearch.xpack.esql.core.tree.Source;
import org.elasticsearch.xpack.esql.core.type.DataType;
import org.elasticsearch.xpack.esql.plan.logical.LogicalPlan;
import org.elasticsearch.xpack.esql.plan.logical.promql.HistogramFunctionCall;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.function.UnaryOperator;

import static java.util.Collections.unmodifiableMap;
import static java.util.Collections.unmodifiableSet;
import static java.util.Collections.unmodifiableSortedSet;
import static org.elasticsearch.xpack.esql.core.expression.Attribute.SYNTHETIC_ATTRIBUTE_NAME_SEPARATOR;
import static org.elasticsearch.xpack.esql.plan.logical.promql.PromqlLabels.PROMETHEUS_LABELS_PREFIX;

/**
 * PromQL translation context: the header of label columns plus value types for intermediate results.
 * <p>
 * Design goals:
 * - Make illegal states unrepresentable (invariants enforced in constructors).
 * - Put behavior on the context (algebra lives on {@link TranslationContext}).
 * - No separate header type: {@code TranslationContext} *is* the header.
 */
public final class TranslationContext {

    private final Set<String> finiteColumns;
    private final SortedSet<Set<String>> openColumns;
    private final Map<String, Attribute> columnExpr;

    private static final Comparator<Set<String>> BY_EXCLUSIONS = Comparator.<Set<String>>comparingInt(Set::size)
        .thenComparing(TranslationContext::mapOpen);

    private TranslationContext(Set<String> finiteColumns, Set<Set<String>> openColumns, Map<String, Attribute> columnExpr) {
        this.finiteColumns = unmodifiableSet(new LinkedHashSet<>(finiteColumns));

        SortedSet<Set<String>> sorted = new TreeSet<>(BY_EXCLUSIONS);
        for (Set<String> ex : openColumns) {
            sorted.add(unmodifiableSet(new LinkedHashSet<>(ex)));
        }
        this.openColumns = unmodifiableSortedSet(sorted);

        // Invariant: bindings must only refer to columns that exist in this context.
        Set<String> allowed = names(this.finiteColumns, this.openColumns);
        if (columnExpr.keySet().stream().anyMatch(name -> allowed.contains(name) == false)) {
            throw new IllegalArgumentException("columnExpr contains names not present in header: " + columnExpr.keySet());
        }
        this.columnExpr = unmodifiableMap(new LinkedHashMap<>(columnExpr));
    }

    // ---------- constants ----------

    /** No columns: a scalar's header, and the identity of {@link #union(TranslationContext[])}. */
    public static final TranslationContext PassThrough = new TranslationContext(Set.of(), Set.of(), Map.of());

    /** The classic-histogram bucket bound as a context, for the histogram functions that consume it. */
    static final TranslationContext _LE = finite(List.of(HistogramFunctionCall.LE_LABEL));

    // ---------- factories ----------

    /** Empty context: no columns. Identity for {@link #union(TranslationContext[])}. */
    public static TranslationContext empty() {
        return new TranslationContext(Set.of(), Set.of(), Map.of());
    }

    /** Exactly these labels as regular columns. */
    public static TranslationContext finite(Collection<String> names) {
        return new TranslationContext(new LinkedHashSet<>(names), Set.of(), Map.of());
    }

    /** One packed column: all runtime labels except {@code exclusions}. */
    public static TranslationContext open(Collection<String> exclusions) {
        return new TranslationContext(Set.of(), Set.of(new LinkedHashSet<>(exclusions)), Map.of());
    }

    /** One packed column: the full label space (no exclusions). */
    public static TranslationContext open() {
        return open(Set.of());
    }

    /** One packed column excluding the regular columns of {@code exclusions}. */
    public static TranslationContext open(TranslationContext exclusions) {
        return open(exclusions.finiteColumns);
    }

    /**
     * Context with all three components set explicitly. Use when building a bound context
     * whose column expressions are already known (e.g. after packing in emitCollapse).
     */
    static TranslationContext of(Set<String> finiteColumns, Set<Set<String>> openColumns, Map<String, Attribute> columnExpr) {
        return new TranslationContext(finiteColumns, openColumns, columnExpr);
    }

    /** Unbound context with only the given open columns; useful when constructing a match key. */
    static TranslationContext ofOpenColumns(Set<Set<String>> openColumns) {
        return new TranslationContext(Set.of(), openColumns, Map.of());
    }

    // ---------- accessors ----------

    public Set<String> finiteColumns() {
        return finiteColumns;
    }

    public SortedSet<Set<String>> openColumns() {
        return openColumns;
    }

    public Map<String, Attribute> columnExpr() {
        return columnExpr;
    }

    public boolean isEmpty() {
        return finiteColumns.isEmpty() && openColumns.isEmpty();
    }

    public boolean isOpen() {
        return openColumns.isEmpty() == false;
    }

    /** True when every column is bound to an attribute. */
    public boolean isBound() {
        return columnExpr.keySet().containsAll(names(finiteColumns, openColumns));
    }

    public Attribute getExpr(String name) {
        return columnExpr.get(name);
    }

    public Attribute getExpr(Set<String> exclusions) {
        return columnExpr.get(mapOpen(exclusions));
    }

    /**
     * Attributes of a bound context as grouping keys:
     * packed columns by increasing exclusions, then regular columns.
     */
    public List<Attribute> expressions() {
        assert isBound() : "invariant: only a bound context has key attributes: " + this;
        var attributes = new ArrayList<Attribute>();
        for (var exclusions : openColumns) {
            attributes.add(getExpr(exclusions));
        }
        for (var name : finiteColumns) {
            attributes.add(getExpr(name));
        }
        return attributes;
    }

    /**
     * Null-fill aliases for columns this context requires but {@code plan} does not produce.
     */
    public List<Alias> nullFills(LogicalPlan plan) {
        var outputs = plan.outputSet();
        return expressions().stream().filter(expr -> outputs.contains(expr) == false).map(TranslationContext::emitNullExpression).toList();
    }

    // ---------- instance algebra ----------

    /**
     * Union of two contexts: columns merged; where both define a binding, the left one wins.
     */
    public TranslationContext union(TranslationContext other) {
        var finite = new LinkedHashSet<>(this.finiteColumns);
        finite.addAll(other.finiteColumns);

        var open = new LinkedHashSet<Set<String>>();
        open.addAll(this.openColumns);
        open.addAll(other.openColumns);

        var exprs = new LinkedHashMap<>(this.columnExpr);
        other.columnExpr.forEach(exprs::putIfAbsent);

        return new TranslationContext(finite, open, exprs);
    }

    /**
     * Transpose this context below a node that drops the columns in {@code dropped}.
     * Regular columns in {@code dropped} are removed; packed columns are widened to exclude them.
     * Stale bindings (for dropped or widened columns) are silently dropped.
     */
    public TranslationContext sub(TranslationContext dropped) {
        var remaining = new LinkedHashSet<>(this.finiteColumns);
        remaining.removeAll(dropped.finiteColumns);

        var widened = new LinkedHashSet<Set<String>>();
        for (var exclusions : this.openColumns) {
            var w = new LinkedHashSet<>(exclusions);
            w.addAll(dropped.finiteColumns);
            widened.add(w);
        }

        // Bindings for dropped finite columns and now-stale open-column canonical names are removed.
        var exprs = new LinkedHashMap<>(this.columnExpr);
        exprs.keySet().retainAll(names(remaining, widened));

        return new TranslationContext(remaining, widened, exprs);
    }

    /**
     * Keep only regular columns that are also in {@code kept}; packed columns unchanged.
     * Bindings for removed columns are silently dropped.
     */
    public TranslationContext filter(TranslationContext kept) {
        var retained = new LinkedHashSet<>(this.finiteColumns);
        retained.retainAll(kept.finiteColumns);

        var exprs = new LinkedHashMap<>(this.columnExpr);
        exprs.keySet().retainAll(names(retained, this.openColumns));

        return new TranslationContext(retained, this.openColumns, exprs);
    }

    /**
     * Select columns that survive a node dropping {@code dropped}:
     * regular columns outside {@code dropped}, packed columns that already exclude all of it.
     * Bindings for removed columns are silently dropped.
     */
    public TranslationContext select(TranslationContext dropped) {
        var remaining = new LinkedHashSet<>(this.finiteColumns);
        remaining.removeAll(dropped.finiteColumns);

        var covering = new LinkedHashSet<Set<String>>();
        for (var exclusions : this.openColumns) {
            if (exclusions.containsAll(dropped.finiteColumns)) {
                covering.add(exclusions);
            }
        }

        var exprs = new LinkedHashMap<>(this.columnExpr);
        exprs.keySet().retainAll(names(remaining, covering));

        return new TranslationContext(remaining, covering, exprs);
    }

    /**
     * Bind this requirement context to the attributes provided by {@code input}.
     * Packed columns must exist in {@code input}; missing regular columns become null-fill references.
     */
    public TranslationContext bind(TranslationContext input) {
        var bound = new LinkedHashMap<String, Attribute>();

        for (var exclusions : this.openColumns) {
            var expr = input.getExpr(exclusions);
            assert expr != null : "invariant: packed column " + exclusions + " must be produced by the input " + input;
            bound.put(mapOpen(exclusions), expr);
        }

        for (var name : this.finiteColumns) {
            var expr = input.getExpr(name);
            bound.put(name, expr != null ? expr : mapToRef(name));
        }

        return new TranslationContext(this.finiteColumns, this.openColumns, bound);
    }

    /**
     * Add or rebind a regular column.
     */
    public TranslationContext bind(String name, Attribute expr) {
        var finite = new LinkedHashSet<>(this.finiteColumns);
        finite.add(name);

        var exprs = new LinkedHashMap<>(this.columnExpr);
        exprs.put(name, expr);

        return new TranslationContext(finite, this.openColumns, exprs);
    }

    /**
     * Add or rebind a packed column.
     */
    public TranslationContext bind(Set<String> exclusions, Attribute expr) {
        var open = new LinkedHashSet<>(this.openColumns);
        open.add(exclusions);

        var exprs = new LinkedHashMap<>(this.columnExpr);
        exprs.put(mapOpen(exclusions), expr);

        return new TranslationContext(this.finiteColumns, open, exprs);
    }

    /**
     * Rebind every attribute through {@code rebind}.
     */
    public TranslationContext map(UnaryOperator<Attribute> rebind) {
        var exprs = new LinkedHashMap<>(this.columnExpr);
        exprs.replaceAll((k, v) -> rebind.apply(v));
        return new TranslationContext(this.finiteColumns, this.openColumns, exprs);
    }

    // ---------- static algebra (forward to instance methods for callers that static-import them) ----------

    public static TranslationContext union(TranslationContext... headers) {
        var result = PassThrough;
        for (var h : headers) {
            result = result.union(h);
        }
        return result;
    }

    public static TranslationContext sub(TranslationContext header, TranslationContext dropped) {
        return header.sub(dropped);
    }

    public static TranslationContext filter(TranslationContext header, TranslationContext kept) {
        return header.filter(kept);
    }

    public static TranslationContext select(TranslationContext header, TranslationContext dropped) {
        return header.select(dropped);
    }

    public static TranslationContext bind(TranslationContext header, TranslationContext input) {
        return header.bind(input);
    }

    public static TranslationContext bind(TranslationContext header, String name, Attribute expr) {
        return header.bind(name, expr);
    }

    public static TranslationContext bind(TranslationContext header, Set<String> exclusions, Attribute expr) {
        return header.bind(exclusions, expr);
    }

    // ---------- helpers ----------

    private static Set<String> names(Set<String> finiteColumns, Set<Set<String>> openColumns) {
        var names = new LinkedHashSet<>(finiteColumns);
        for (var ex : openColumns) {
            names.add(mapOpen(ex));
        }
        return names;
    }

    static Alias emitNullExpression(Attribute attribute) {
        var nullLiteral = new Literal(attribute.source(), null, attribute.resolved() ? attribute.dataType() : DataType.KEYWORD);
        return new Alias(attribute.source(), attribute.name(), nullLiteral, attribute.id());
    }

    // ---------- equality ----------

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj instanceof TranslationContext other) {
            return finiteColumns.equals(other.finiteColumns)
                && openColumns.equals(other.openColumns)
                && columnExpr.equals(other.columnExpr);
        }
        return false;
    }

    @Override
    public int hashCode() {
        return Objects.hash(finiteColumns, openColumns, columnExpr);
    }

    @Override
    public String toString() {
        return "TranslationContext{finite=" + finiteColumns + ", open=" + openColumns + ", exprs=" + columnExpr.keySet() + "}";
    }

    // ---------- IR ----------

    /**
     * The result of translating a PromQL AST node: a plan plus its exposed columns and numeric value.
     * <p>
     * Invariants:
     * - context is bound;
     * - every context expression belongs to the plan's output.
     */
    public static final class IntermediateResult {

        private final LogicalPlan plan;
        private final TranslationContext context;
        private final Expression value;
        private final Attribute step;
        private final Expression pendingFilter;
        private final Kind kind;

        public enum Kind {
            BEFORE_INITIAL_AGGREGATE(false, false),
            AFTER_INITIAL_AGGREGATE(true, false),
            CONSTANT(true, true);

            public final boolean constant;
            public final boolean afterInitialAggregation;

            Kind(boolean afterInitialAggregation, boolean constant) {
                this.afterInitialAggregation = afterInitialAggregation;
                this.constant = constant;
            }
        }

        IntermediateResult(
            LogicalPlan plan,
            TranslationContext context,
            Expression value,
            Attribute step,
            Expression pendingFilter,
            Kind kind
        ) {
            Objects.requireNonNull(plan, "plan");
            Objects.requireNonNull(context, "context");
            Objects.requireNonNull(step, "step");
            Objects.requireNonNull(kind, "kind");

            assert context.isBound() : "invariant: a translated table binds every column of its context: " + context;
            assert context.columnExpr().values().stream().allMatch(plan.outputSet()::contains)
                : "invariant: column expressions must belong to the output of " + plan;

            this.plan = plan;
            this.context = context;
            this.value = value;
            this.step = step;
            this.pendingFilter = pendingFilter;
            this.kind = kind;
        }

        // ---------- convenient factories that encode valid states ----------

        /** Scalar/local relation before any aggregation. */
        public static IntermediateResult scalar(LogicalPlan plan, Expression value, Attribute step) {
            return new IntermediateResult(plan, PassThrough, value, step, null, Kind.BEFORE_INITIAL_AGGREGATE);
        }

        /** Scalar with a pending label matcher filter. */
        public static IntermediateResult scalar(LogicalPlan plan, Expression value, Attribute step, Expression selectorFilter) {
            return new IntermediateResult(plan, PassThrough, value, step, selectorFilter, Kind.BEFORE_INITIAL_AGGREGATE);
        }

        /** Aggregated table with explicit context. */
        public static IntermediateResult aggregated(LogicalPlan plan, TranslationContext context, Attribute valueColumn, Attribute step) {
            return new IntermediateResult(plan, context, valueColumn, step, null, Kind.AFTER_INITIAL_AGGREGATE);
        }

        /** Constant (aggregation-free) local relation. */
        public static IntermediateResult constant(LogicalPlan plan, TranslationContext context, Attribute valueColumn, Attribute step) {
            return new IntermediateResult(plan, context, valueColumn, step, null, Kind.CONSTANT);
        }

        // ---------- accessors ----------

        public LogicalPlan plan() {
            return plan;
        }

        public TranslationContext context() {
            return context;
        }

        public Expression value() {
            return value;
        }

        public Attribute step() {
            return step;
        }

        public Expression pendingFilter() {
            return pendingFilter;
        }

        public Kind kind() {
            return kind;
        }

        /** The value as a defined column; valid only when the value is an attribute. */
        public Attribute valueColumn() {
            return (Attribute) value;
        }

        public Attribute getExpr(String name) {
            return context.getExpr(name);
        }

        public Attribute getExpr(Set<String> exclusions) {
            return context.getExpr(exclusions);
        }

        /**
         * Rebuild around a new plan and value, keeping context and other properties.
         */
        public IntermediateResult with(LogicalPlan plan, Expression value) {
            return new IntermediateResult(plan, context, value, step, pendingFilter, kind);
        }

        /**
         * Rebuild around a new plan, context and value, keeping other properties.
         */
        public IntermediateResult with(LogicalPlan plan, TranslationContext context, Expression value) {
            return new IntermediateResult(plan, context, value, step, pendingFilter, kind);
        }
    }

    // ---------- Name mapping helpers ----------

    static String mapOpen() {
        return mapOpen(Set.of());
    }

    static String mapOpen(Set<String> exclusions) {
        var s = String.join(SYNTHETIC_ATTRIBUTE_NAME_SEPARATOR, new TreeSet<>(exclusions));
        return MetadataAttribute.TIMESERIES + (s.isEmpty() ? s : SYNTHETIC_ATTRIBUTE_NAME_SEPARATOR + s);
    }

    static List<String> mapFinite(Collection<? extends Attribute> attributes) {
        return attributes.stream().map(TranslationContext::mapFinite).distinct().toList();
    }

    static String mapFinite(Attribute attribute) {
        String name = attribute instanceof FieldAttribute field ? field.fieldName().string() : attribute.name();
        return name.startsWith(PROMETHEUS_LABELS_PREFIX) ? name.substring(PROMETHEUS_LABELS_PREFIX.length()) : name;
    }

    static Attribute mapToRef(String name) {
        return new ReferenceAttribute(Source.EMPTY, null, name, DataType.KEYWORD);
    }

    public static Attribute find(List<Attribute> attributes, String label) {
        Attribute bareMatch = null;
        for (Attribute attribute : attributes) {
            if (mapFinite(attribute).equals(label)) {
                if (attribute.name().equals(label) == false) {
                    return attribute;
                }
                bareMatch = attribute;
            }
        }
        return bareMatch;
    }

    public static Attribute find(List<Attribute> attributes, Set<String> excluded) {
        for (var attr : attributes) {
            if (attr instanceof TimeSeriesMetadataAttribute ma) {
                if (ma.excludedFields().equals(excluded)) {
                    return ma;
                }
            }
        }
        return null;
    }
}
