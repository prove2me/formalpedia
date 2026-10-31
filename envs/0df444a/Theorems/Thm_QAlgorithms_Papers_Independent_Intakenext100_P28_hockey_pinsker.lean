-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_hockey_pinsker
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.hockey_pinsker
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:41:42.552383+00:00
-- url     : https://prove2.me/theorems/fa8ed4f3-4c77-4bdf-915b-351c45cf68ef
-- title:
--   Theorem 32: E_gamma log gamma<=D+2e^{-1}log e, and 2 E_gamma^2 log e<=D
-- statement:
--   For probability measures on a common space and $\gamma\ge1$,
--
--   $$E_\gamma(P\|Q)\log_b\gamma\le D(P\|Q)+2e^{-1}\log_b e,
--   \qquad 2E_\gamma(P\|Q)^2\log_b e\le D(P\|Q).$$
--
--   Here $e$ is the natural exponential constant. The first bound is attributed to [68, Proposition 13]; the second reduces to Pinsker at $\gamma=1$.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 61, Theorem 32

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 32: E_gamma log gamma<=D+2e^{-1}log e, and 2 E_gamma^2 log e<=D. Sason--Verdu, arXiv:1508.00335v7, PDF p.61.  -/
theorem hockey_pinsker
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (g : ℝ) (hg : 1 ≤ g) :
    hockey g P Q * ENNReal.ofReal (logB b g) ≤ kl b P Q + ENNReal.ofReal (2 * Real.exp (-1) * logBaseE b) ∧
    2 * hockey g P Q ^ 2 * ENNReal.ofReal (logBaseE b) ≤ kl b P Q := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
