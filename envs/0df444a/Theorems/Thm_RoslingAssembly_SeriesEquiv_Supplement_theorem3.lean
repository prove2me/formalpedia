-- Prove2me | Theorems.Thm_RoslingAssembly_SeriesEquiv_Supplement_theorem3
-- name    : RoslingAssembly.SeriesEquiv.Supplement.theorem3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:21:51.844011+00:00
-- url     : https://prove2.me/theorems/53c5f765-4d6f-4b54-b120-2c4d95883076
-- title:
--   Theorem 3 — complete aggregation and eventual optimality of the full lift
-- statement:
--   Under GA and the standing assembly-model assumptions, run the complete aggregation procedure that eliminates a nonpositive-holding-cost item $i$ into any shortest-lead immediate predecessor $n$ whose sibling predecessors all have positive holding coefficients. Every step uses the simultaneous data assignments in the aggregation definition.
--
--   1. Every actual elimination strictly decreases the number of active items. From every reachable state the procedure reaches a terminal state. Every terminal state admits a valid source indexing of the reduced tree, and under every valid source indexing the reduced system satisfies both clauses of the positive-holding-cost Assumption.
--   2. Let $C$ and $D$ be the surviving and eliminated labels of any terminal state, with representatives resolved through all later eliminations. If the reduced reorder levels $S_i$, $i\in C$, eventually become optimal for the reduced system, there exists a feasible policy for the original system which, after an almost-sure finite transient, simultaneously obeys
--   $$
--   Y_{it}=\begin{cases}\min(S_i,X^{M-M_i}_{kt})&X_{it}\le S_i,\\ X_{it}&X_{it}>S_i,\end{cases}
--   \quad(i\in C),\qquad
--   Y_{it}=X^{M-M_i}_{n(i),t}\quad(i\in D),
--   $$
--   and every subsequent continuation is optimal from the actual remaining pipeline. Here $k$ is the next surviving item in the valid reduced order and $n(i)$ is the ultimate surviving representative. At the last survivor the first branch is $S_i$.
--
--   This companion theorem extends the source's series-policy construction to nonpositive echelon costs. It includes arbitrary shortest-lead ties, zero lead times, the zero-step case, arbitrary well-formed initial pipelines and both discounted and limiting average criteria; it does not prescribe a globally discounted-optimal transient.
--
--   **Formalization Note** The full two-branch rule uses final reduced order transported back to original labels. Part (ii) is asserted for every valid indexing of the reduced tree, so it contains the source's order $k=\min\{l\in C: l>i\}$ on original labels whenever that order is a valid indexing (in particular, the identity when nothing is eliminated). No bounded-demand, initial-balance, finite-optimum or optimal-policy-existence hypothesis is added.
--
--   Differences from the source:
--   - encoding: the physical assembly model of §§1–2 → the published Model, Policy, Dynamics and Cost, with H1 = sum h, nonnegative backlogging cost, a probability demand law and a well-formed initial pipeline; reason: these are the physical coefficient and feasible-history conventions; no initial long-run balance is imposed
--   - reading: optimality at alpha = 1 means the normalized limit of (2), including (4) → HasAverageCost asserts the actual extended-valued limit; optimality compares feasible policies whose source criterion is defined; reason: neither a nonexistent limit nor infinity minus infinity has a source value; existence of the optimizer and its criterion remains a conclusion
--   - encoding: periods t = 1, 2, ... and inventory ages → decisions use k = t - 1 observed demands, with item-specific ages M_k - mu; reason: this is the published finite-history and forward-time convention
--   - reading: eventually, with the positive-mean-demand argument on pp. 572–573 → one policy and one almost-sure finite path-dependent transient for every later period and every clause; reason: positive iid mean makes accumulated demand exceed every finite bound almost surely; no deterministic bound is printed
--   - generalization: items indexed by increasing total lead time and successors before predecessors; k = Min{l ∈ C / l > i} on original labels → a valid indexing of the reduced tree exists, and parts (i)–(ii) hold under every valid bijective indexing of the surviving labels; reason: arbitrary equal-lead ties can make the original-label order invalid after reattachment; quantifying over every valid indexing contains the source's order whenever it is valid, so nothing is weakened
--   - reading: the reorder levels eventually become optimal for the aggregated system → for every reduced initial pipeline, a feasible reduced prefix followed by the rule and optimal continuations; reason: the levels are system-wide reorder levels; the premise refers only to the reduced system, never the original conclusion
--   - encoding: the minimum over later surviving items at the final item → an absent upper cap is positive infinity, so the final first branch equals its level; reason: this is the unconstrained outside-supplier boundary, and does not set an empty real infimum to zero
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4):565–579, 1989, DOI 10.1287/opre.37.4.565, p. 572 (PDF 9), Theorem 3; proof p. 573 (PDF 10)

import Definitions.Def_RoslingAssembly_SeriesEquiv_Supplement_Lift

namespace RoslingAssembly.SeriesEquiv.Supplement
open MeasureTheory

theorem theorem3 (S : Model) [IsProbabilityMeasure S.ν] (x0 : InitialPositions)
    (hStanding : Standing S x0) (hGA : GeneralizedAssumption S) :
    (∀ A B : AggregationState, Reachable S A → AggregationStep S A B →
      B.active.card < A.active.card) ∧
    (∀ A : AggregationState, Reachable S A →
      ∃ B : AggregationState, Relation.ReflTransGen (AggregationStep S) A B ∧ B.Terminal) ∧
    (∀ A : AggregationState, Reachable S A → A.Terminal →
      (∃ e : ℕ → ℕ, A.Relabeling e ∧ (A.reduced S e).ValidTree) ∧
      (∀ i ∈ Finset.Icc 1 S.N, A.representative i ∈ A.active) ∧
      ∀ e : ℕ → ℕ, A.Relabeling e → (A.reduced S e).ValidTree →
        (A.reduced S e).Assumption ∧
        ∀ levels : ℕ → ℝ,
          EventuallyOptimalLevels (A.reduced S e) (fun r => levels (e r)) →
            EventuallyOptimalLift S A e levels x0) := by sorry

end RoslingAssembly.SeriesEquiv.Supplement
