-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P89_resourceEnergyBoundary
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P89.resourceEnergyBoundary
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:20:17.114593+00:00
-- url     : https://prove2.me/theorems/98f37255-29e1-4ca3-9a32-c25a3e4b2439
-- title:
--   Resource-energy divergence and finite-energy attainment branches
-- statement:
--   Fix finite $r>0$, put $L=\tanh r$ and $U=1/\tanh r$, and let $b_{\min}(\tau)$ be the bound in (9). Define $a_{\min}(\tau)$ and $\overline n_{\min}(\tau)$ from the same family at $b=b_{\min}$. All three functions are continuous on $(L,U)$, and
--
--   $$a_{\min}(\tau),\ b_{\min}(\tau),\ \overline n_{\min}(\tau)\longrightarrow+\infty\quad\text{as }\tau\to L^+\text{ or }\tau\to U^-.$$
--
--   For the attainment classification, allow any finite $r\ge0$. For every $\lambda>0$, let $(\tau_{\rm opt},y_{\rm opt})$ be the optimizer of (13), and let $s=e^{2r}/(e^r+\lambda\cosh r)^2$. If $s\le\tanh r$, including equality, then $r>0$ and
--
--   $$\tau_{\rm opt}=\tanh r,\qquad y_{\rm opt}=1-\tanh r,$$
--
--   and this channel has no finite-energy centered Gaussian BK realization with logarithmic negativity exactly $2r$. If $\tanh r<s$, such a finite-energy realization exists.
--
--   The divergence is expressed through one-sided limits, without evaluating the rational family at a singular endpoint or introducing an infinite-energy density. The $r=0$ vacuum-replacer endpoint is not a divergence case.
-- source:
--   Optimal continuous variable quantum teleportation with limited resources, arXiv:1705.03017v5, PDF p. 3, Energy divergence at the quantum-limited boundary of Eq. (9)

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

/-- PDF pp.3--4, after (9) and (13): divergence is a one-sided LIMIT,
never a density or a rational expression evaluated at a zero denominator.
For r=0 the vacuum replacer endpoint is excluded from divergence. -/
theorem resourceEnergyBoundary (r : ℝ) (hr : 0 ≤ r) :
    (0 < r →
      let low := Real.tanh r
      let high := (Real.tanh r)⁻¹
      let interval := Set.Ioo low high
      ContinuousOn (familyMinA r) interval ∧
      ContinuousOn (familyMinB r) interval ∧
      ContinuousOn (familyMinEnergy r) interval ∧
      Tendsto (familyMinA r) (nhdsWithin low interval) atTop ∧
      Tendsto (familyMinB r) (nhdsWithin low interval) atTop ∧
      Tendsto (familyMinEnergy r) (nhdsWithin low interval) atTop ∧
      Tendsto (familyMinA r) (nhdsWithin high interval) atTop ∧
      Tendsto (familyMinB r) (nhdsWithin high interval) atTop ∧
      Tendsto (familyMinEnergy r) (nhdsWithin high interval) atTop) ∧
    (∀ lambda : ℝ, 0 < lambda →
      (stationaryTau lambda r ≤ Real.tanh r →
        0 < r ∧ optimalTau lambda r = Real.tanh r ∧
        optimalNoise lambda r = 1 - Real.tanh r ∧
        ¬ FiniteBKSimulates r (optimalTau lambda r) (optimalNoise lambda r)) ∧
      (Real.tanh r < stationaryTau lambda r →
        FiniteBKSimulates r (optimalTau lambda r) (optimalNoise lambda r))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P89

end
