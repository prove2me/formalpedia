-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P75_squeezed_epr_variance_limit
-- name    : QAlgorithms.Papers.Independent.Intake100.P75.squeezed_epr_variance_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:04:50.701519+00:00
-- url     : https://prove2.me/theorems/dc937a82-eeb7-45e0-883f-6486956d1618
-- title:
--   Physical squeezing makes the EPR variance tend to zero
-- statement:
--   For $r\ge0$, let $\psi_r=\exp[-r(a_1^\dagger a_2^\dagger-a_1a_2)]|0,0\rangle$ be the two-mode squeezed vacuum on the completed oscillator space. Each finite-$r$ vector is normalized. With $[x_j,p_k]=i\delta_{jk}$ and extended variances,
--
--   $$
--   \lim_{r\to+\infty}\left[\operatorname{Var}_{|\psi_r\rangle\langle\psi_r|}(x_1+x_2)+\operatorname{Var}_{|\psi_r\rangle\langle\psi_r|}(p_1-p_2)\right]=0.
--   $$
--
--   The formal vector is the accepted squeezedVector evaluated at $-r$, matching the printed negative generator. The limiting ideal EPR co-eigenstate is not asserted to be a normalized vector.
-- source:
--   Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, PDF p. 1, Motivating paragraph; generator on p.5

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

/-- PDF p.1, motivating squeezed-EPR limit; p.5 fixes the negative generator.
The vector is normalized at every finite r>=0, including vacuum at r=0.
The extended variances, without clipping, tend to zero as r tends to infinity;
no nonnormalizable ideal EPR vector is introduced. -/
theorem squeezed_epr_variance_limit :
    (∀ r : ℝ, 0 ≤ r → ‖squeezedVector (-r)‖ = 1) ∧
    Tendsto (fun r : ℝ => eprTotalVariance (rankOne (squeezedVector (-r))) 1)
      atTop (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P75

end
