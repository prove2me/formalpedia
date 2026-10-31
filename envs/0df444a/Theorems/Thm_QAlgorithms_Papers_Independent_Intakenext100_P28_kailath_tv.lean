-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_kailath_tv
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.kailath_tv
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:36:30.235037+00:00
-- url     : https://prove2.me/theorems/ea99b6d8-dd02-425c-95ea-14d13fd1060f
-- title:
--   Theorem 19: TV^2/4<=1-exp(-D_(1/2)(P||Q))
-- statement:
--   For arbitrary probability measures on a common measurable space,
--
--   $$\frac{|P-Q|^2}{4}\le1-\exp_b[-D_{1/2}(P\|Q)].$$
--
--   The exponential term is the square of the Hellinger affinity $\int\sqrt{pq}\,d(P+Q)$, which also covers singular pairs. This classical bound is attributed to Kailath [55, (99)]. No finite-alphabet assumption is imposed.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 38, Theorem 19

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 19: TV^2/4<=1-exp(-D_(1/2)(P||Q)). Sason--Verdu, arXiv:1508.00335v7, PDF p.38.  -/
theorem kailath_tv
    {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    fullVariation P Q ^ 2 / 4 ≤ 1 -
      (∫⁻ x, ENNReal.ofReal (Real.sqrt (rnDensityReal P (P + Q) x * rnDensityReal Q (P + Q) x)) ∂(P + Q)) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
