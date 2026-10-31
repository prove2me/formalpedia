-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_finite_covariance_ellipsoid
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.finite_covariance_ellipsoid
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:45:42.064833+00:00
-- url     : https://prove2.me/theorems/0df1ea82-dd30-45a2-8971-249532e62134
-- title:
--   Example 5.1: finite-dimensional covariance ellipsoid
-- statement:
--   Let $W$ be a centered Gaussian vector in $\mathbb R^k$ with covariance matrix $\Sigma$, possibly singular. Its covariance RKHS and unit ball satisfy
--   $$H_W=\operatorname{range}\Sigma,\qquad\langle\Sigma g,\Sigma h\rangle_H=g^T\Sigma h,\qquad H_1=\{\Sigma h:h^T\Sigma h\le1\}.$$
--   If $\Sigma$ is nonsingular this is the ellipsoid $x^T\Sigma^{-1}x\le1$. Singular covariance retains only its range directions, including the zero space when $k=0$.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 15, Example 5.1: finite-dimensional covariance ellipsoid

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

section MoreResults

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP

/-- Example 5.1: finite-dimensional covariance ellipsoid, arXiv:0805.3252v1, PDF p.15.
The finite Cartesian space uses its standard coordinate Banach model; covariance RKHSs and their H norms are unchanged by equivalent finite-dimensional ambient norms. k=0 and singular matrices are included. -/
theorem finite_covariance_ellipsoid
(k : ℕ) (W : Omega → (Fin k → ℝ)) (hW : BorelCenteredGaussianElement P W)
    (sigma : Matrix (Fin k) (Fin k) ℝ)
    (hcov : ∀ i j, ∫ o, W o i * W o j ∂P = sigma i j) :
    banachRKHS P W = Set.range sigma.mulVec ∧
    (∀ g h : Fin k → ℝ,
      banachInner P W (sigma.mulVec g) (sigma.mulVec h) =
        ∑ i, g i * (sigma.mulVec h) i) ∧
    rkhsUnitBall P W =
      {x | ∃ h : Fin k → ℝ, x = sigma.mulVec h ∧ ∑ i, h i * (sigma.mulVec h) i ≤ 1} ∧
    (IsUnit sigma.det → rkhsUnitBall P W =
      {x | ∑ i, x i * (sigma⁻¹.mulVec x) i ≤ 1}) := by sorry

end MoreResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
