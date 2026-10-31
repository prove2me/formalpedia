-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P75_high_temperature_lifetime
-- name    : QAlgorithms.Papers.Independent.Intake100.P75.high_temperature_lifetime
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:07:12.035337+00:00
-- url     : https://prove2.me/theorems/d4085a8f-0131-4034-9e55-630d1102c116
-- title:
--   High-temperature lifetime asymptotics and sufficient separability time
-- statement:
--   Hold $r>0$ and $\eta>0$ fixed. Let $T(r,\eta,\bar n)$ be the exact positive-temperature lifetime in Eq. (20). Then
--
--   $$
--   \lim_{\bar n\to+\infty}\bar n\,T(r,\eta,\bar n)=\frac{1-e^{-2r}}{4\eta}.
--   $$
--
--   Moreover, for each $\bar n>0$ and finite $t\ge0$, the actual independently attenuated two-mode squeezed output is separable whenever
--
--   $$
--   t\ge\frac{1-e^{-2r}}{4\eta\bar n}.
--   $$
--
--   The sufficient inequality follows from the preceding exact lifetime and remains valid for all positive occupations. It is not a finite-temperature equality or an equivalence. The fixed squeezing and damping parameters precede the varying bath occupation.
-- source:
--   Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, PDF p. 5, Final thermal-noise sentence

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P75

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P75

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsSeparable IsBarycenter rankOne productCoeff)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel GaussianWithCovariance standardFormCovariance
   modeCovarianceBlock productWeyl CharacteristicSummable multimodeWeylTrace
   covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Next46.P45
  (TwoMode PureVector Decomposes ladderCoefficients squeezedVector
   squeezedCoefficients GaussianShiftLaw shiftArgument)

open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel partialRight)

open QAlgorithms.Papers.Independent.Frontier18.P14 (occupationOutput)

open QAlgorithms.Papers.Independent.Gap48.P26 (thermalKernel)

local instance : MeasurableSpace TwoMode := borel TwoMode

/-- PDF p.5, final thermal-noise sentence, interpreted through exact (20).
At fixed r,eta>0, nbar*T tends to (1-exp(-2r))/(4 eta). The printed sufficient
separability inequality is valid for every positive nbar, since log(1+x)<=x;
it is not asserted to be a finite-temperature equivalence. -/
theorem high_temperature_lifetime
    (r eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    Tendsto (fun nbar : ℝ => nbar * thermalLifetime r eta nbar) atTop
      (𝓝 ((1 - Real.exp (-2 * r)) / (4 * eta))) ∧
    (∀ nbar t : ℝ, 0 < nbar → 0 ≤ t →
      (1 - Real.exp (-2 * r)) / (4 * eta * nbar) ≤ t →
      IsSeparable (thermalOutput r eta nbar t)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P75

end
