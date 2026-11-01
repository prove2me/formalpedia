-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P89_broadPriorLimit
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P89.broadPriorLimit
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:22:53.56053+00:00
-- url     : https://prove2.me/theorems/75681188-2a9b-4d3c-826f-1f115af62b7f
-- title:
--   One-sided broad-prior limit and TMSS covariance
-- statement:
--   Fix finite $r\ge0$. For every $\lambda>0$ use the normalized Gaussian prior, and let $\tau_{\rm opt}(\lambda,r)$, $y_{\rm opt}(\lambda,r)$ and $\overline F_{\rm opt}(\lambda,r)$ be the optimizer and independently defined scalar maximum. As $\lambda\to0$ through positive values,
--
--   $$\tau_{\rm opt}\to1,\qquad y_{\rm opt}\to2e^{-2r},\qquad \overline F_{\rm opt}\to\frac1{1+e^{-2r}}.$$
--
--   The minimum-family coefficients (9), evaluated at $\tau_{\rm opt}$, obey
--
--   $$a_{\min},b_{\min}\to\cosh(2r),\qquad c_{\min}\to\sinh(2r),\qquad \sqrt{\tau_{\rm opt}}\to1.$$
--
--   These are the pure TMSS covariance and unit displacement gain. This expresses the broad-prior limit of normalized ensembles, without asserting a uniform probability measure on $\mathbb C$ or substituting $\lambda=0$ in (12). The source identifies the limiting fidelity with earlier results [17,29] and the unit-gain BK protocol [9].
-- source:
--   Optimal continuous variable quantum teleportation with limited resources, arXiv:1705.03017v5, PDF p. 4, Broad-prior one-sided limit of the optimum, Eq. (15)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P89

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P89

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel tensorApply traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P39
  (coherentKet coherentCoefficient operatorOfMatrix husimiQ HasFockMatrix CoherentRealized)

open QAlgorithms.Papers.Independent.Frontier30.P14 (weylCharacteristic)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel PhysicalCovariance CharacteristicSummable
   multimodeWeylTrace covarianceCharacteristicValue standardFormCovariance)

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

open QAlgorithms.Papers.Independent.Gap48.P26 (PhaseInsensitive coherentKernel)

open QAlgorithms.Entanglement (partialTransposeFirst)

/-- PDF p.4, (15): one-sided broad-prior limit of normalized lambda>0
ensembles and minimum-family covariances, not a uniform probability on C.
This recovers the cited earlier results [17,29] and unit-gain BK [9]. -/
theorem broadPriorLimit (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (fun lambda => optimalTau lambda r) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) ∧
    Tendsto (fun lambda => optimalNoise lambda r) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (2 * Real.exp (-2 * r))) ∧
    Tendsto (fun lambda => scalarOptimum lambda r) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (1 / (1 + Real.exp (-2 * r)))) ∧
    Tendsto (fun lambda => familyMinA r (optimalTau lambda r)) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (Real.cosh (2 * r))) ∧
    Tendsto (fun lambda => familyMinB r (optimalTau lambda r)) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (Real.cosh (2 * r))) ∧
    Tendsto (fun lambda => familyMinC r (optimalTau lambda r)) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (Real.sinh (2 * r))) ∧
    Tendsto (fun lambda => Real.sqrt (optimalTau lambda r)) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P89

end
