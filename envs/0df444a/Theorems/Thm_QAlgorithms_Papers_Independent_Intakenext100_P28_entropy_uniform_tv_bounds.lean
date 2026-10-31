-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_entropy_uniform_tv_bounds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.entropy_uniform_tv_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:55:26.197731+00:00
-- url     : https://prove2.me/theorems/1cbf14e6-d68e-409e-9b6f-779aec669bdc
-- title:
--   Entropy versus uniform-TV bounds (385)–(387)
-- statement:
--   Let $P$ be a law on $M>1$ symbols and $U$ the uniform law. Then
--
--   $$H(P)\le\log_bM-\tfrac12|P-U|^2\log_b e,$$
--
--   $$H(P)\le\log_bM+\log_b(1-|P-U|^2/4),\qquad
--   H(P)\ge\log_bM-\log_b(1+M|P-U|^2/2).$$
--
--   These are all three companion entropy inequalities (385)–(387). The logarithm argument in the second is positive since the finite-uniform distance is less than 2.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 54, Entropy versus uniform-TV bounds (385)–(387)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Entropy versus uniform-TV bounds (385)–(387). Sason--Verdu, arXiv:1508.00335v7, PDF p.54.  -/
theorem entropy_uniform_tv_bounds
    (b : LogBase) (n : ℕ) (hn : 1 < n) (p : Fin n → ℝ) (hp : FiniteProbabilityLaw p) :
    shannonEntropyBase b p ≤ logB b n - finiteTV p (uniformLaw n) ^ 2 * logBaseE b / 2 ∧
    shannonEntropyBase b p ≤ logB b n + logB b (1 - finiteTV p (uniformLaw n) ^ 2 / 4) ∧
    logB b n - logB b (1 + (n : ℝ) * finiteTV p (uniformLaw n) ^ 2 / 2) ≤ shannonEntropyBase b p := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
