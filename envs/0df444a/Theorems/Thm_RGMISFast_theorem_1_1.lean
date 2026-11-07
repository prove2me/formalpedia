-- Prove2me | Theorems.Thm_RGMISFast_theorem_1_1
-- name    : RGMISFast.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:27:49.994227+00:00
-- url     : https://prove2.me/theorems/f5d7d740-040a-44d9-9316-814cd247580e
-- title:
--   Theorem 1.1: $\Pr[Q(u^*)>C\Delta^{90}(1+h)]\le e^{-h}$ and $E[Q(u^*)]\le 2C\Delta^{90}$
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $G=(V,E)$ be a finite simple undirected graph with maximum degree at most $\Delta\ge2$, with independent Exp(1) ranks. For every vertex $u^*$ fixed before the ranks are sampled and every $h\ge0$, the number $Q(u^*)$ of fresh calls of the memoized, pruned Procedure 1.1 started at $u^*$ satisfies
--   $$
--   \Pr\big[Q(u^*)>C\Delta^{90}(1+h)\big]\le e^{-h}, \tag{1}
--   $$
--   and consequently
--   $$
--   \mathbb E[Q(u^*)]\le 2C\Delta^{90}.
--   $$
--
--   This answers the question of Nguyen and Onak on the local query complexity of randomized greedy MIS from a worst-case vertex: polynomial in $\Delta$, independent of the size of the graph.
--
--   **Formalization Note** $C$ is chosen before the vertex type, the graph, $\Delta$, the root and $h$, and the same $C$ serves both clauses. $Q(u^*)$ is the fresh-call counter of the explicit procedure; rank ties (probability zero) are broken by a fixed order on $V$, and the theorem holds for every such order.
--
--   Differences from the source:
--   - encoding: Q(u∗), the number of fresh calls of RGMIS(G, r, u∗) → `Q G u r`, the fresh-call counter of the explicit memoized recursion `run`, rank ties broken by the order on V (any LinearOrder V); reason: ties have probability zero; for distinct ranks the order on V plays no role
--   - generalization: the tail and expectation bounds → the bounds plus the clause `Measurable (Q G u)`; reason: a true added clause that makes the lower integral the expectation; dropping it gives the printed theorem
--   - encoding: Pr[·] and E[Q(u∗)] → outer measure of {Q > C∆^90(1+h)} under `rankLaw V`; lower Lebesgue integral of Q as an extended nonnegative real; reason: with Q measurable these are the probability and the expectation
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), Theorem 1.1, eq. (1), p.3 (PDF p.5)

import Mathlib
import Definitions.Def_RGMISFast_run
import Definitions.Def_RGMISFast_rankLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RGMISFast

/-- Theorem 1.1 (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…), p.3): for a finite simple graph with maximum degree at most `∆ ≥ 2` and
i.i.d. Exp(1) ranks, for every root `u∗` fixed before the ranks are sampled and every `h ≥ 0`,
`Pr[Q(u∗) > C∆^90(1 + h)] ≤ e^{−h}`, where `C` is an absolute constant; consequently
`E[Q(u∗)] ≤ 2C∆^90`.

**Formalization Note** `C` is chosen before the vertex type, the graph, `∆`, the root and `h`,
and the same `C` serves both clauses. `∆` is a bound on every degree. `Q` is the fresh-call
counter of the memoized, pruned Procedure 1.1 (`RGMISFast.Q`); rank ties, which have probability
zero, are broken by the order on `V`, and the statement holds for every such order. The law of the
ranks is `rankLaw V`, the product of Exp(1) laws. The tail is the (outer) measure of the set
`{Q > C∆^90(1+h)}`; the expectation is the lower Lebesgue integral of `Q` as an extended
nonnegative real, made the honest expectation by the added clause `Measurable Q`. -/
theorem theorem_1_1 : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type) [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ),
      2 ≤ Δ → (∀ v, G.degree v ≤ Δ) → ∀ u : V,
        Measurable (fun r : V → ℝ => Q G u r) ∧
        (∀ h : ℝ, 0 ≤ h →
          rankLaw V {r | C * (Δ : ℝ) ^ 90 * (1 + h) < (Q G u r : ℝ)} ≤
            ENNReal.ofReal (Real.exp (-h))) ∧
        ∫⁻ r, (Q G u r : ℝ≥0∞) ∂(rankLaw V) ≤ ENNReal.ofReal (2 * C * (Δ : ℝ) ^ 90) := by sorry

end RGMISFast
