-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_five_tv_constants
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.five_tv_constants
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:30:31.545505+00:00
-- url     : https://prove2.me/theorems/f7e04903-e4d2-4d49-9c0d-4770e1092656
-- title:
--   Corollary 1: The five sharp TV ratios are: H_alpha:1/[2(1-alpha)] for 0<alpha<1; Delta:1; JS:log 2; d2sq(P,Q):1/2; d2sq(P,Q)+d2sq(Q,P):1
-- statement:
--   With full L1 total variation, the sharp universal coefficients comparing each numerator to $|P-Q|$ are
--
--   $$H_\alpha:\frac1{2(1-\alpha)}\ (0<\alpha<1),\quad
--   \Delta:1,\quad JS:\log_b2,\quad d_2^2(P,Q):\frac12,\quad
--   d_2^2(P,Q)+d_2^2(Q,P):1.$$
--
--   The first four comparisons range over $P\ll Q$; the last ranges over mutually absolutely continuous probability pairs. All alphabets are allowed. These are all five equations (144)–(148).
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 22, Corollary 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Corollary 1: The five sharp TV ratios are: H_alpha:1/[2(1-alpha)] for 0<alpha<1; Delta:1; JS:log 2; d2sq(P,Q):1/2; d2sq(P,Q)+d2sq(Q,P):1. Sason--Verdu, arXiv:1508.00335v7, PDF p.22.  -/
theorem five_tv_constants
    (b : LogBase) :
    (∀ a : ℝ, 0 < a → a < 1 →
      Sharp (hellinger a) fullVariation acPairs (ENNReal.ofReal (1 / (2 * (1 - a))))) ∧
    Sharp triangular fullVariation acPairs 1 ∧ Sharp (js b) fullVariation acPairs (ENNReal.ofReal (logB b 2)) ∧
    Sharp marton fullVariation acPairs (1 / 2) ∧ Sharp martonSum fullVariation mutualPairs 1 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
