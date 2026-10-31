-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_cayley_phase_law
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.cayley_phase_law
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:55:21.114319+00:00
-- url     : https://prove2.me/theorems/ce40cccf-e66d-4b9d-ab40-c48b58c6feba
-- title:
--   Appendix B: Cayley/Siegel-disc coordinate under phase shifts
-- statement:
--   For a valid finite Gaussian graph $Z$, define its Cayley coordinate $K=(I+iZ)(I-iZ)^{-1}$. For arbitrary local phases $\theta_j$, put $E=\operatorname{diag}(e^{-i\theta_j})$. The input and transformed Cayley denominators are invertible, and
--
--   $$K'=EKE.$$
--
--   The vacuum $Z=iI$, for which $K=0$, is included. No inverse of $K$ is required, so the result covers every valid graph.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 21, Appendix B: Cayley/Siegel-disc coordinate under phase shifts

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF pp.21–22, (B1)–(B5): Cayley coordinate transforms by
left/right exp(-i theta). Vacuum has K=0 and is included; K^{-1} is not assumed. -/
theorem cayley_phase_law {I : Type*} [Fintype I] [DecidableEq I]
    (Z : Matrix I I ℂ) (hZ : ValidGraph Z) (theta : I → ℝ) :
    let E := Matrix.diagonal (fun j => Complex.exp (-Complex.I * (theta j : ℂ)))
    IsUnit (1 - Complex.I • Z).det ∧
    IsUnit (1 - Complex.I • graphPhaseMobius Z theta).det ∧
    siegelDiscCoordinate (graphPhaseMobius Z theta) = E * siegelDiscCoordinate Z * E := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
