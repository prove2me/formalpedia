-- Prove2me | Theorems.Thm_RobustFcstAgg_Supplement_theorem_2
-- name    : RobustFcstAgg.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:40:28.67612+00:00
-- url     : https://prove2.me/theorems/fd14d246-1325-4d72-ba8e-854a07f8710d
-- title:
--   Theorem 2 — a difference aggregation rule with $n$ queries and order and agent complexity at most $n$ recovers $Y$
-- statement:
--   In the partial information model with $n$ experts, there is a single deterministic aggregation rule $R=(\mathcal Q,f)$, chosen without knowledge of the instance, such that:
--
--   1. $R$ is a **difference aggregation rule**: $\mathcal Q=\mathcal Q_{\mathrm{diff}(L)}$ for some ordered list $L$ of experts and $f$ is Borel-measurable;
--   2. one DAG $G$ elicits $\mathcal Q$ and witnesses both $\text{agent-c}(R)\le n$ and $\text{order-c}(R)\le n$;
--   3. $\text{query-c}(R)=|\mathcal Q|=n$;
--   4. $R$ **implements** $A^*$: for every partial-information instance $\mathcal D$,
--   $$
--   f(\mathcal Q)=A^*=Y\qquad\mathcal D\text{-almost surely.}$$
--
--   Asking each expert what they add to the earlier experts' estimate thus recovers all information with $n$ queries instead of the $2^n-1$ intersection queries of Theorem 1.
--
--   **Formalization Note** In the partial information model $A^*=Y$. Elicitation is the base `IsDAGElicits` (with Condition 1). The query count $n$ forces $|L|=n$.
--
--   Differences from the source:
--   - generalization: DAG-elicitable (Definition 3) → the eliciting DAG also satisfies Condition 1, with one payment π for all instances D and a payment integrable on a.e. fibre for every report; reason: a stronger conclusion, which implies the printed one; the quadratic-score payments of Proposition 2 and 4 meet each clause (p.25 notes the Brier score satisfies Condition 1)
--   - encoding: implements A* (A = f(Q) almost surely, A* = E[Y | X1, …, Xm]) → the rule is fixed first, and for every instance D, R.output D = Y D-almost surely; reason: A* = Y in the partial information model (p.8); the principal does not know D (p.4)
--   - encoding: Q = Q_diff(L) for some ordered list L → some L : List (Fin n) and a bijection of the rule's index with Fin L.length under which each query is diffColl L; reason: an indexed collection up to relabelling; the same rule
--   - reading: diff(i1, …, ik) := E[Y − Σ diff(i1, …, ik−j) | Sk] → conditioning on S_{i_k}, the last expert of the list; reason: Proposition 3 and the proof of Proposition 4 (p.23) condition on S_{i_k}; S_k is a typo for it
--   - encoding: order-c(R) ≤ n and agent-c(R) ≤ n, witnessed by a single DAG G → one out-neighbour map with every walk from a query of length ≤ n and at most n experts reachable from each query; reason: the definitions of p.6 for a witnessing DAG
--   - encoding: [n], E[· | S_i], X_∅ = 0 → Fin n; integrals over the hidden signals; nonempty T only; reason: same instances; conditioning is by independence of the signals
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Theorem 2, p.11

import Mathlib
import Definitions.Def_RobustFcstAgg_Supplement_HasDiffQueries
import Definitions.Def_RobustFcstAgg_IsDAGElicits
import Definitions.Def_RobustFcstAgg_OrderLE
import Definitions.Def_RobustFcstAgg_AgentLE
import Definitions.Def_RobustFcstAgg_Rule_output
import Definitions.Def_RobustFcstAgg_InfoStruct_jointLaw
open MeasureTheory

namespace RobustFcstAgg.Supplement

/-- **Theorem 2.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*,
arXiv:2512.05271, Theorem 2, p.11: "There exists a deterministic difference aggregation rule `R` that implements `A*` with
`agent-c(R) ≤ n`, `order-c(R) ≤ n`, and `query-c(R) = n`. Each complexity measure bound is simultaneously witnessed by a
single DAG `G` that elicits `R`."

**Formalization Note.** The rule is chosen before the instance `D`. "Implements `A*`" is `R.output D = Y` `D`-a.s. for every
`D` (`A* = Y`, p.8). A difference aggregation rule (Definition 7) is a rule with queries `Q_diff(L)` for some list `L`
(`HasDiffQueries R`), Borel `f` (bundled in `Rule`), and an eliciting DAG; the one DAG `out` witnesses elicitation (with
Condition 1) and both bounds. `query-c(R) = n` is `Fintype.card R.ι = n`, which forces `|L| = n`. -/
theorem theorem_2 (n : ℕ) :
    ∃ R : Rule n, HasDiffQueries R ∧
      (∃ out : R.ι → Finset (Option R.ι),
        IsDAGElicits R.Q out ∧ OrderLE out n ∧ AgentLE R.Q out n) ∧
      Fintype.card R.ι = n ∧
      ∀ D : InfoStruct n, R.output D =ᵐ[D.jointLaw] Y := by sorry

end RobustFcstAgg.Supplement
