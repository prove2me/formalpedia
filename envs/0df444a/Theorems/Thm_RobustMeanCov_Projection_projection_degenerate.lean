-- Prove2me | Theorems.Thm_RobustMeanCov_Projection_projection_degenerate
-- name    : RobustMeanCov.Projection.projection_degenerate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:44:09.698301+00:00
-- url     : https://prove2.me/theorems/af7bdff1-d00d-44ca-a22c-e17d4dcdeacf
-- title:
--   If $x'\Sigma x = 0$ then $x'\mathbf R \equiv x'\mu$ almost surely
-- statement:
--   Let $\mu, x \in \mathbb{R}^n$ and let $\Sigma$ be a real $n\times n$ matrix with $x'\Sigma x = 0$. Then for every law $P \in \mathbb{M}^n_{(\mu,\Sigma)}$,
--
--   $$
--   x'R = x'\mu \quad \text{for } P\text{-almost every } R .
--   $$
--
--   This is the degenerate case of the general projection property: when the projected variance vanishes, every feasible $\mathbf R$ projects onto the constant $\mu_x$, and the univariate class $\mathbb{M}_{(\mu_x,0)}$ consists of the point mass at $\mu_x$ alone.
--
--   **Formalization Note** The statement holds for every matrix $\Sigma$; positive semidefiniteness is not assumed because it is not used.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, https://doi.org/10.1287/opre.1060.0353, p. 109, Appendix, proof of Theorem 1, first sentence

import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

/-- Appendix, proof of Theorem 1, first sentence (Popescu 2007, p. 109): if `x′Σx = 0`, then
`x′R ≡ x′μ` almost surely for every law `R ∼ (μ, Σ)`. -/
theorem projection_degenerate {n : ℕ} (μ x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hq : x.ofLp ⬝ᵥ S *ᵥ x.ofLp = 0)
    (P : Measure (EuclideanSpace ℝ (Fin n))) (hP : P ∈ MeanCovClass μ S) :
    ∀ᵐ R ∂P, ⟪x, R⟫ = ⟪x, μ⟫ := by sorry

end RobustMeanCov.Projection
