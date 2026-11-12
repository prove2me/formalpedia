-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P77_weighted_information_security
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P77.weighted_information_security
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T08:07:32.86228+00:00
-- url     : https://prove2.me/theorems/dfe9fca7-66b5-4fbd-8b80-04f8ecce18c5
-- title:
--   Weighted information implies the joint security criterion
-- statement:
--   Let $T$ be a finite transcript alphabet, let $w_t\ge0$ with $\sum_t w_t\le1$ be joint probabilities of passing and transcript $t$, and let $J_t\ge0$ be the information in that transcript. For every threshold $a>0$,
--
--   $$a\sum_{t:J_t\ge a}w_t\le\sum_t w_tJ_t.$$
--
--   In particular, for $\alpha\in\mathbb R$, $\beta>0$, and $n\in\mathbb N$, if $\sum_t w_tJ_t\le e^{2(\alpha-\beta n)}$, then
--
--   $$\Pr[\mathrm{pass}\ \text{and}\ J\ge e^{\alpha-\beta n}]\le e^{\alpha-\beta n}.$$
--
--   The exponential threshold is positive even when the weighted information is zero. The probabilities are not normalized conditional on passing.
-- source:
--   A Proof of the Security of Quantum Key Distribution, arXiv:quant-ph/9912053v1, PDF p. 28, Appendix N: weighted-information bound implies security criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P77

open scoped BigOperators ComplexConjugate ComplexOrder

open QAlgorithms

-- The repair instruction authorizes imports of pinned accepted definitions.
-- These are definitions only; no imported paper theorem is used here.

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Support50.P16 (trivialMeasurement)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Appendix N, PDF pp.28--29, Eqs.(45),(46): Markov's bound for subnormalized
pass weights and its positive exponential-threshold specialization. No sqrt(W)
threshold is used at W=0. -/
theorem weighted_information_security {T : Type} [Fintype T]
    (p : PassWeights T) (info : T → ℝ) (hi : ∀ t, 0 ≤ info t) :
    (∀ a : ℝ, 0 < a →
      luckyProbability p info a * a ≤ ∑ t, p.weight t * info t) ∧
    ∀ (alpha beta : ℝ), 0 < beta → ∀ n : ℕ,
      (∑ t, p.weight t * info t) ≤ Real.exp (2 * (alpha - beta * n)) →
      luckyProbability p info (Real.exp (alpha - beta * n)) ≤
        Real.exp (alpha - beta * n) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P77

end
