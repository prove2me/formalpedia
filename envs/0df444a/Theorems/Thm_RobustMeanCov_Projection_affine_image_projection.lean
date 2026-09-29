-- Prove2me | Theorems.Thm_RobustMeanCov_Projection_affine_image_projection
-- name    : RobustMeanCov.Projection.affine_image_projection
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:46:53.246985+00:00
-- url     : https://prove2.me/theorems/cc7df896-ee9f-43db-92b0-32cb30c69041
-- title:
--   $x'(\mu+\Sigma^{1/2}Z) = x'\mu + (x'\Sigma x)^{1/2}\, y'Z$
-- statement:
--   Let $\mu, x\in\mathbb{R}^n$, let $\Sigma$ be a real positive semidefinite $n\times n$ matrix with $x'\Sigma x>0$, and let $y = (x'\Sigma x)^{-1/2}\Sigma^{1/2}x$. Then for every $Z\in\mathbb{R}^n$,
--
--   $$
--   x'(\mu + \Sigma^{1/2} Z) = x'\mu + (x'\Sigma x)^{1/2}\, y'Z .
--   $$
--
--   Combined with the standardization $\mathbf z = (x'\Sigma x)^{-1/2}(\mathbf r - x'\mu)$ and a lift $\mathbf z = y'\mathbf Z$, this identity shows that $\mathbf R = \mu + \Sigma^{1/2}\mathbf Z$ projects onto the prescribed $\mathbf r$.
--
--   **Formalization Note** The paper's "pathwise" identity $x'\mathbf R = x'\mu + (x'\Sigma x)^{1/2}\mathbf z$ is stated as a pointwise algebraic identity in $Z$. The hypothesis $x'\Sigma x > 0$ is the case the proof is in after its first sentence and keeps the real powers $(x'\Sigma x)^{\pm 1/2}$ away from their default values.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, https://doi.org/10.1287/opre.1060.0353, p. 110, Appendix, proof of Theorem 1, final sentence ('x′R = x′μ + (x′Σx)^{1/2}z = r (pathwise)')

import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

/-- Appendix, proof of Theorem 1, final sentence (Popescu 2007, p. 110): with
`y = (x′Σx)^{-1/2} Σ^{1/2} x`, every `Z` satisfies
`x′(μ + Σ^{1/2} Z) = x′μ + (x′Σx)^{1/2} y′Z`. -/
theorem affine_image_projection {n : ℕ} (μ x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) (hq : 0 < x.ofLp ⬝ᵥ S *ᵥ x.ofLp)
    (Z : EuclideanSpace ℝ (Fin n)) :
    let y : EuclideanSpace ℝ (Fin n) :=
      (x.ofLp ⬝ᵥ S *ᵥ x.ofLp) ^ (-(1 / 2 : ℝ)) • toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x
    ⟪x, μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) Z⟫ =
      ⟪x, μ⟫ + (x.ofLp ⬝ᵥ S *ᵥ x.ofLp) ^ (1 / 2 : ℝ) * ⟪y, Z⟫ := by sorry

end RobustMeanCov.Projection
