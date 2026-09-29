-- Prove2me | Theorems.Thm_RobustMeanCov_Projection_normalized_direction_inner_self
-- name    : RobustMeanCov.Projection.normalized_direction_inner_self
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:45:13.55101+00:00
-- url     : https://prove2.me/theorems/55b99621-e101-4d6f-90c5-2558cb21e8ac
-- title:
--   The direction $y = (x'\Sigma x)^{-1/2}\Sigma^{1/2}x$ is a unit vector
-- statement:
--   Let $\Sigma$ be a real positive semidefinite $n\times n$ matrix with positive semidefinite square root $\Sigma^{1/2}$, and let $x\in\mathbb{R}^n$ satisfy $x'\Sigma x > 0$. Define
--
--   $$
--   y = (x'\Sigma x)^{-1/2}\, \Sigma^{1/2} x \qquad (\text{so } y' = (x'\Sigma x)^{-1/2} x'\Sigma^{1/2}).
--   $$
--
--   Then $y'y = 1$; in particular $y \neq 0$.
--
--   This is the normalization that lets the proof of the general projection property reduce to projecting an isotropic random vector onto a unit direction.
--
--   **Formalization Note** $\Sigma^{1/2}$ is `CFC.sqrt S`, acting on $\mathbb{R}^n$ through `Matrix.toEuclideanCLM`, exactly as in Mathlib's `multivariateGaussian`. $y'y$ is the Euclidean inner product $\langle y, y\rangle$.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, https://doi.org/10.1287/opre.1060.0353, p. 109, Appendix, proof of Theorem 1, 'Note that y′y = 1' (before (2))

import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

/-- Appendix, proof of Theorem 1 (Popescu 2007, p. 109): for `Σ ⪰ 0` and `x′Σx > 0`, the vector
`y = (x′Σx)^{-1/2} Σ^{1/2} x` satisfies `y′y = 1`. -/
theorem normalized_direction_inner_self {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) (hq : 0 < x.ofLp ⬝ᵥ S *ᵥ x.ofLp) :
    let y : EuclideanSpace ℝ (Fin n) :=
      (x.ofLp ⬝ᵥ S *ᵥ x.ofLp) ^ (-(1 / 2 : ℝ)) • toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x
    ⟪y, y⟫ = 1 := by sorry

end RobustMeanCov.Projection
