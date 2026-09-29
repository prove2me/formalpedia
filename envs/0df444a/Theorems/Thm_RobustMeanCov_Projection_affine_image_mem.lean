-- Prove2me | Theorems.Thm_RobustMeanCov_Projection_affine_image_mem
-- name    : RobustMeanCov.Projection.affine_image_mem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:46:14.113066+00:00
-- url     : https://prove2.me/theorems/16992b06-2d3e-44cc-82eb-09214386f065
-- title:
--   If $\mathbf Z\sim(0,I_n)$ and $\Sigma\succeq 0$ then $\mu+\Sigma^{1/2}\mathbf Z\sim(\mu,\Sigma)$
-- statement:
--   Let $\mu\in\mathbb{R}^n$, let $\Sigma$ be a real positive semidefinite $n\times n$ matrix with positive semidefinite square root $\Sigma^{1/2}$, and let $Q\in \mathbb{M}^n_{(0,I_n)}$. If $\mathbf Z$ has law $Q$, then
--
--   $$
--   \mathbf R = \mu + \Sigma^{1/2}\mathbf Z
--   $$
--
--   has a law in $\mathbb{M}^n_{(\mu,\Sigma)}$.
--
--   This is the step that turns the isotropic lift into a feasible random vector of the original mean-covariance class.
--
--   **Formalization Note** $\Sigma^{1/2}$ is `CFC.sqrt S` acting through `Matrix.toEuclideanCLM`, as in Mathlib's `multivariateGaussian`. The law of $\mathbf R$ is the pushforward of $Q$ under the continuous affine map $Z\mapsto \mu+\Sigma^{1/2}Z$. The hypothesis $\Sigma\succeq 0$ is Theorem 1's.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, https://doi.org/10.1287/opre.1060.0353, p. 110, Appendix, proof of Theorem 1, final sentence ('Defining R = μ + Σ^{1/2}Z')

import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

/-- Appendix, proof of Theorem 1, final sentence (Popescu 2007, p. 110): if `Z ∼ (0, Iₙ)` and
`Σ ⪰ 0`, then `R = μ + Σ^{1/2} Z ∼ (μ, Σ)`. -/
theorem affine_image_mem {n : ℕ} (μ : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef)
    (Q : Measure (EuclideanSpace ℝ (Fin n)))
    (hQ : Q ∈ MeanCovClass (0 : EuclideanSpace ℝ (Fin n)) (1 : Matrix (Fin n) (Fin n) ℝ)) :
    Q.map (fun Z => μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) Z) ∈ MeanCovClass μ S := by sorry

end RobustMeanCov.Projection
