-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P75_thermal_noise_separability_lifetime
-- name    : QAlgorithms.Papers.Independent.Intake100.P75.thermal_noise_separability_lifetime
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:05:44.213747+00:00
-- url     : https://prove2.me/theorems/e083d58c-5d8e-4d73-aa93-046e8fccff71
-- title:
--   Thermal-noise separability lifetime
-- statement:
--   Fix squeezing $r>0$, damping rate $\eta>0$, and common bath occupation $\bar n>0$. Send the two modes of $\exp[-r(a_1^\dagger a_2^\dagger-a_1a_2)]|0,0\rangle$ through independent thermal attenuators with intensity transmissivity $\tau=e^{-2\eta t}$ at finite time $t\ge0$. Each attenuator is defined by a beam-splitter dilation with an independent Gibbs environment of mean occupation $\bar n$. Let $\rho_t$ be the resulting actual density. Define
--
--   $$
--   T(r,\eta,\bar n)=\frac{1}{2\eta}\log\left(1+\frac{1-e^{-2r}}{2\bar n}\right).
--   $$
--
--   Then $\rho_t$ is entangled if and only if $t<T(r,\eta,\bar n)$, and it is separable if and only if $t\ge T(r,\eta,\bar n)$. In particular, equality belongs to the separable branch. The output is computed from the input density and the channels, rather than assumed to have a desired covariance.
-- source:
--   Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, PDF p. 5, Application, Eq. (20)

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

/-- PDF p.5, (20) and the immediately following sentence: both branches of the
finite thermal lifetime, including separability at equality. The output is the
actual independent thermal-channel dilation of the printed squeezed vector.
The source's opposite correlation sign is a local pi-phase convention and does
not alter either separability branch. No covariance formula is assumed. -/
theorem thermal_noise_separability_lifetime
    (r eta nbar t : ℝ) (hr : 0 < r) (heta : 0 < eta) (hnbar : 0 < nbar) (ht : 0 ≤ t) :
    IsDensity (thermalOutput r eta nbar t) ∧
    (¬ IsSeparable (thermalOutput r eta nbar t) ↔ t < thermalLifetime r eta nbar) ∧
    (IsSeparable (thermalOutput r eta nbar t) ↔ thermalLifetime r eta nbar ≤ t) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P75

end
