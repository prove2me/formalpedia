-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_phase_stationarity
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.phase_stationarity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:46:02.257148+00:00
-- url     : https://prove2.me/theorems/75f8c038-7859-4ac4-8861-828ca8e1708b
-- title:
--   IV.A and Appendix B: phase stationarity criterion
-- statement:
--   For a valid finite Gaussian graph $Z=V+iU$, let $E_Z(\theta)=\tfrac12\operatorname{tr}\operatorname{Im}Z(\theta)$ after independent local phase rotations. For each coordinate $j$,
--
--   $$\operatorname{Im}(Z^2)_{jj}=2(UV)_{jj},\qquad \left.\frac{\partial E_Z}{\partial\theta_j}\right|_0=-(UV)_{jj}.$$
--
--   Consequently, if $(UV)_{jj}=0$ for every $j$, then the full first derivative of $E_Z$ vanishes at zero. This is stationarity, the meaning used by Appendix B, and does not exclude saddles. The printed missing factor two is corrected.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 13, IV.A and Appendix B: phase stationarity criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF pp.13–14,22, (4.3),(B8): stationarity, not a claim that
vanishing first derivatives exclude saddles. The printed missing factor 2 in
Im(Z^2)_jj=2(UV)_jj is corrected here. -/
theorem phase_stationarity {I : Type*} [Fintype I] [DecidableEq I]
    (Z : Matrix I I ℂ) (hZ : ValidGraph Z) :
    (∀ j, imagPart (Z * Z) j j = 2 * (imagPart Z * realPart Z) j j) ∧
    (∀ j, HasDerivAt (fun s : ℝ => phaseError Z (Pi.single j s))
      (-(imagPart Z * realPart Z) j j) 0) ∧
    ((∀ j, (imagPart Z * realPart Z) j j = 0) →
      HasFDerivAt (phaseError Z) (0 : (I → ℝ) →L[ℝ] ℝ) 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
