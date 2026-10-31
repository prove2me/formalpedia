-- Prove2me | Theorems.Thm_PandoraComb_observation_1
-- name    : PandoraComb.observation_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:27.258852+00:00
-- url     : https://prove2.me/theorems/515f97be-8784-4b09-a668-5874dbc424be
-- title:
--   Observation 1 — for every order $\sigma$, some threshold strategy is optimal among fixed order $\sigma$ strategies (corrected: thresholds in $\mathbb R\cup\{+\infty\}$)
-- statement:
--   Let $\mathcal I=(D_1,\dots,D_n,c)$ be an instance: independent non-negative values with finite expectations, and a cost $c$ with $c(\emptyset)=0$ that is monotone. Let $\sigma$ be any ordering of the boxes.
--
--   Then there are thresholds $t_0,\dots,t_{n-1}\in\mathbb R\cup\{\pm\infty\}$ such that the fixed order strategy with thresholds $(\sigma,t)$ is admissible and
--   $$u(\mathcal I;\pi)\ \le\ u\big(\mathcal I;(\sigma,t)\big)$$
--   for every admissible strategy $\pi$ with fixed order $\sigma$, randomized strategies included.
--
--   In words: the best strategy that inspects boxes in the order $\sigma$ only has to decide when to stop, and it stops exactly when the best value seen so far reaches a threshold that depends on the round. Theorem 4.1 combines this with the fact that, for submodular costs, some fixed order strategy is optimal.
--
--   Differences from the source:
--   - correction: fixed order strategy with thresholds t_1, …, t_n ∈ ℝ (p.7) → thresholds t : Fin n → EReal (a threshold +∞ never halts); reason: with real thresholds the statement is false: two i.i.d. Exp(1) boxes, c ≡ 0; opening both is optimal (utility 3/2), but any real t_2 halts after one box with positive probability and loses utility; the proof of Observation 1 (p.33) itself sets t_i = ∞ when C_i = ∅
--   - encoding: rounds i = 1, …, n, permutation σ : [n] → [n], "maximum value inspected so far" (p.7) → rounds k = 0, …, n−1, σ : Fin n ≃ ι, halt at round k iff t k ≤ max(0, maximum observed so far); reason: index shift only; the maximum so far is 0 before the first box, as in the proof of Observation 1 (x ≥ 0, p.33)
--   - reading: "the optimal strategy with fixed order σ is a fixed order strategy with thresholds" → the strategy of the stated form is admissible and its utility is at least that of every admissible strategy with fixed order σ; reason: this says that an optimal strategy with fixed order σ exists and that one is of the stated form, without presupposing an optimum
--   - encoding: Π, all (randomized) strategies, deciding from the sequence of opened boxes and realized values so far, with coins tossed a priori (p.7) → admissible strategies: decisions read the ordered history and one uniform seed s ∈ [0,1] independent of the values, and are measurable in the observed values and the seed; reason: one uniform seed generates any finite family of coin tosses; measurability is what makes E[V(π)] and E[c(S(π))] defined, and it holds for every strategy the paper uses
--   - encoding: V(π) = max over S(π) of V_i, u(π) = E[V(π)] − E[c(S(π))] (p.7) → reward max(0, max observed value), utility = expectation of reward minus c(set of opened boxes); reason: values are non-negative a.s. and the empty strategy has utility 0 (pp.8, 24), so the two rewards agree a.s.
--   - encoding: boxes [n], c : 2^[n] → ℝ≥0 normalized and monotone (p.7) → boxes a finite type ι, c : Finset ι → ℝ with c ∅ = 0 and Monotone c; reason: relabeling [n] as ι changes no instance; c ≥ 0 follows from c ∅ = 0 and monotonicity
--   - encoding: a strategy chooses an uninspected box or halts (p.7) → a request for an already opened box halts the run; at most |ι| rounds; reason: a legal strategy never makes such a request, and |ι| rounds suffice to open every box
-- source:
--   Berger, Ezra, Feldman & Fusco, Pandora’s Problem with Combinatorial Cost, arXiv:2303.01078v1, Observation 1, p.7 (proof in Appendix D, p.33)

import Definitions.Def_PandoraComb_Model
import Definitions.Def_PandoraComb_FixedOrder

open MeasureTheory

namespace PandoraComb

/-- **Observation 1** (arXiv:2303.01078v1, p.7; proof in Appendix D, p.33): "For every
permutation σ, the optimal strategy with fixed order σ is a fixed order strategy with
thresholds."

**Formalization Note.** The instance is `IsInstance D c` (§2, p.7); no submodularity. For every
order `σ` there are thresholds `t` such that the threshold strategy `(σ, t)` is admissible and its
utility is at least that of every admissible strategy with fixed order `σ` (randomized ones
included). Thresholds take values in `EReal`, as the proof's `t_i = ∞ if C_i = ∅` (p.33)
requires. -/
theorem observation_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ι → Measure ℝ)
    (c : Finset ι → ℝ) (hI : IsInstance D c) (σ : Fin (Fintype.card ι) ≃ ι) :
    ∃ t : Fin (Fintype.card ι) → EReal,
      Admissible (thresholdStrategy σ t) ∧
        ∀ π : Strategy ι, Admissible π → IsFixedOrder σ π →
          utility D c π ≤ utility D c (thresholdStrategy σ t) := by sorry

end PandoraComb
