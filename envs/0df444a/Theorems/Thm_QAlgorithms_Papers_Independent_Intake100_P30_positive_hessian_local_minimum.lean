-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_positive_hessian_local_minimum
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.positive_hessian_local_minimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:46:38.07247+00:00
-- url     : https://prove2.me/theorems/997b57e2-c0ae-4fac-9591-84c29f8c9094
-- title:
--   IV.A and Appendix B: positive Hessian suffices for a strict local minimum
-- statement:
--   Let $Z=V+iU$ be valid, with $(UV)_{jj}=0$ for every mode. Let $\circ$ denote entrywise matrix multiplication and assume
--
--   $$H=\operatorname{Im}[(I+Z^2)\circ Z]>0.$$
--
--   Then zero local phase shift is a strict local minimum of $E_Z(\theta)=\tfrac12\operatorname{tr}\operatorname{Im}Z(\theta)$: there is $\delta>0$ such that $0<\|\theta\|<\delta$ implies $E_Z(0)<E_Z(\theta)$. Positive semidefiniteness alone is not used to infer a minimum.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 14, IV.A and Appendix B: positive Hessian suffices for a strict local minimum

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF pp.14,22, (4.4),(B15): positive definite Hessian at a
stationary phase gives a strict local minimum; semidefiniteness is insufficient. -/
theorem positive_hessian_local_minimum {I : Type*} [Fintype I] [DecidableEq I]
    (Z : Matrix I I ℂ) (hZ : ValidGraph Z)
    (hStationary : ∀ j, (imagPart Z * realPart Z) j j = 0)
    (hH : (phaseHessian Z).PosDef) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ theta : I → ℝ,
      0 < ‖theta‖ → ‖theta‖ < delta → phaseError Z 0 < phaseError Z theta := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
