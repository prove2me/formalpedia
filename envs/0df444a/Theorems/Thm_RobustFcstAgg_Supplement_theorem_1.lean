-- Prove2me | Theorems.Thm_RobustFcstAgg_Supplement_theorem_1
-- name    : RobustFcstAgg.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:39:22.156174+00:00
-- url     : https://prove2.me/theorems/6694f070-3371-4f7b-94f9-eb5de4debf38
-- title:
--   Theorem 1 — an intersection aggregation rule with $2^n-1$ queries and order and agent complexity at most $n$ recovers $Y$
-- statement:
--   In the partial information model with $n$ experts, there is a single deterministic aggregation rule $R=(\mathcal Q,f)$, chosen without knowledge of the instance, such that:
--
--   1. $R$ is an **intersection aggregation rule**: $\mathcal Q=\mathcal Q_{\mathrm{inter}(n)}=(\mathrm{inter}(S))_{\emptyset\ne S\subseteq[n]}$ and $f$ is Borel-measurable;
--   2. one DAG $G$ elicits $\mathcal Q$ and witnesses both $\text{order-c}(R)\le n$ and $\text{agent-c}(R)\le n$;
--   3. $\text{query-c}(R)=|\mathcal Q|=2^n-1$;
--   4. $R$ **implements** $A^*$: for every partial-information instance $\mathcal D$,
--   $$
--   f(\mathcal Q)=A^*=Y\qquad\mathcal D\text{-almost surely.}$$
--
--   So optimal aggregation is possible under truthful, DAG-elicitable queries, at the price of exponentially many queries; Theorem 2 brings the count down to $n$.
--
--   **Formalization Note** In the partial information model $A^*=\mathbb E[Y\mid X]=Y$. Elicitation is the base `IsDAGElicits` (with Condition 1). The printed "$2n-1$" of the text layer is $2^n-1=\sum_{k=1}^n\binom nk$.
--
--   Differences from the source:
--   - generalization: DAG-elicitable (Definition 3) → the eliciting DAG also satisfies Condition 1, with one payment π for all instances D and a payment integrable on a.e. fibre for every report; reason: a stronger conclusion, which implies the printed one; the quadratic-score payments of Proposition 2 and 4 meet each clause (p.25 notes the Brier score satisfies Condition 1)
--   - encoding: implements A* (A = f(Q) almost surely, A* = E[Y | X1, …, Xm]) → the rule is fixed first, and for every instance D, R.output D = Y D-almost surely; reason: A* = Y in the partial information model (p.8); the principal does not know D (p.4)
--   - encoding: Q = Q_inter(n), indexed by the nonempty subsets S → a bijection of the rule's index with InterIndex n n under which each query is interQuery S; reason: an indexed collection up to relabelling; the same rule
--   - reading: agent(inter(S)) is an expert of S → the minimum of S (base interQuery); reason: every choice gives the same random variable and the same complexities
--   - encoding: order-c(R) ≤ n and agent-c(R) ≤ n, witnessed by a single DAG G → one out-neighbour map with every walk from a query of length ≤ n and at most n experts reachable from each query; reason: the definitions of p.6 for a witnessing DAG
--   - encoding: [n], E[· | S_i], X_∅ = 0 → Fin n; integrals over the hidden signals; nonempty T only; reason: same instances; conditioning is by independence of the signals
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Theorem 1, p.9 (proof Appendix A, p.23)

import Mathlib
import Definitions.Def_RobustFcstAgg_Supplement_HasInterQueries
import Definitions.Def_RobustFcstAgg_IsDAGElicits
import Definitions.Def_RobustFcstAgg_OrderLE
import Definitions.Def_RobustFcstAgg_AgentLE
import Definitions.Def_RobustFcstAgg_Rule_output
import Definitions.Def_RobustFcstAgg_InfoStruct_jointLaw
open MeasureTheory

namespace RobustFcstAgg.Supplement

/-- **Theorem 1.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*,
arXiv:2512.05271, Theorem 1, p.9 (proof App. A, p.23): "There exists a deterministic intersection aggregation rule `R` that
implements `A*` with `query-c(R) = 2^n − 1`, `agent-c(R) ≤ n`, and `order-c(R) ≤ n`. Each complexity measure bound is
simultaneously witnessed by a single DAG `G` that elicits `R`."

**Formalization Note.** The rule is chosen before the instance `D` (the principal does not know `D`, p.4). "Implements `A*`"
is `R.output D = Y` `D`-a.s. for every `D`, since `A* = E[Y | X] = Y` in the partial information model (p.8). An
intersection aggregation rule (Definition 5) is a rule with queries `Q_inter(n)` (`HasInterQueries R n`), Borel `f`
(bundled in `Rule`), and an eliciting DAG; the one DAG `out` witnesses elicitation (with Condition 1) and both bounds.
`2n −1` in the text layer is `2^n − 1`. -/
theorem theorem_1 (n : ℕ) :
    ∃ R : Rule n, HasInterQueries R n ∧
      (∃ out : R.ι → Finset (Option R.ι),
        IsDAGElicits R.Q out ∧ OrderLE out n ∧ AgentLE R.Q out n) ∧
      Fintype.card R.ι = 2 ^ n - 1 ∧
      ∀ D : InfoStruct n, R.output D =ᵐ[D.jointLaw] Y := by sorry

end RobustFcstAgg.Supplement
