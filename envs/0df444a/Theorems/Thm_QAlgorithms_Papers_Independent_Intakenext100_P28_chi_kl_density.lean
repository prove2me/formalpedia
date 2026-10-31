-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_chi_kl_density
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.chi_kl_density
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:49:46.972839+00:00
-- url     : https://prove2.me/theorems/cfe4f178-a1ff-4e8e-891c-435f35ee2a33
-- title:
--   Corollary 8: chi2(P||Q)<=beta1^{-1}sqrt(min{D/(2log e),1-exp(-D)})
-- statement:
--   If $\beta_1>0$, then
--
--   $$\chi^2(P\|Q)\le\beta_1^{-1}\sqrt{\min\left\{
--   \frac{D(P\|Q)}{2\log_b e},\ 1-\exp_b(-D(P\|Q))\right\}}.$$
--
--   The square root covers the whole minimum and $\beta_1^{-1}$ lies outside it. Density boundedness makes KL finite. The case $\beta_1=1$, hence $P=Q$, is included.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 70, Corollary 8

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Corollary 8: chi2(P||Q)<=beta1^{-1}sqrt(min{D/(2log e),1-exp(-D)}). Sason--Verdu, arXiv:1508.00335v7, PDF p.70.  -/
theorem chi_kl_density
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hb : 0 < inverseUpperDensity P Q) :
    chiSquareDiv P Q ≤ ENNReal.ofReal ((inverseUpperDensity P Q)⁻¹ * Real.sqrt
      (min ((kl b P Q).toReal / (2 * logBaseE b))
        (1 - expB b (-(kl b P Q).toReal)))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
