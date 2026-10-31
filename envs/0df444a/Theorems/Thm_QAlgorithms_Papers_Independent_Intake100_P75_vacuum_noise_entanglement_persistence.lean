-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P75_vacuum_noise_entanglement_persistence
-- name    : QAlgorithms.Papers.Independent.Intake100.P75.vacuum_noise_entanglement_persistence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:06:21.688218+00:00
-- url     : https://prove2.me/theorems/abe8b6e8-3b1d-4059-aa17-534a6eae5361
-- title:
--   Zero-temperature persistence at every finite time
-- statement:
--   Fix $r>0$ and a damping rate $\eta>0$. Let $\rho_t$ be the actual output obtained by independently transmitting both modes of the printed two-mode squeezed vacuum through vacuum-environment attenuators of intensity transmissivity $e^{-2\eta t}$. For every finite real time $t\ge0$,
--
--   $$
--   \rho_t\text{ is a normalized density and is entangled.}
--   $$
--
--   Zero temperature is treated separately from the logarithmic formula with positive bath occupation. There is no finite entanglement-death time; the limiting infinite-time product vacuum does not contradict this finite-time statement.
-- source:
--   Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, PDF p. 5, Paragraph following Eq. (20)

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

/-- PDF p.5, vacuum-fluctuation paragraph: every finite nonnegative time retains
entanglement at zero bath occupation. This is a separate zero-temperature branch,
not evaluation of the logarithmic expression with a zero denominator. -/
theorem vacuum_noise_entanglement_persistence
    (r eta t : ℝ) (hr : 0 < r) (heta : 0 < eta) (ht : 0 ≤ t) :
    IsDensity (thermalOutput r eta 0 t) ∧
    ¬ IsSeparable (thermalOutput r eta 0 t) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P75

end
