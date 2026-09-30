-- Prove2me | Theorems.Thm_RobustMeanCov_Projection_general_projection_property
-- name    : RobustMeanCov.Projection.general_projection_property
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:47:25.956591+00:00
-- url     : https://prove2.me/theorems/0038d53a-d141-4d60-bf98-a26920908c4a
-- title:
--   Theorem 1 (General Projection Property): $R\mapsto x'R$ maps $\mathbb{M}^n_{(\mu,\Sigma)}$ onto $\mathbb{M}_{(x'\mu,\,x'\Sigma x)}$
-- statement:
--   Let $\mu\in\mathbb{R}^n$, let $\Sigma$ be a real positive semidefinite $n\times n$ matrix, and let $x\in\mathbb{R}^n$ be nonzero. Write $\mu_x = x'\mu$ and $\sigma_x^2 = x'\Sigma x$. Consider the $x$-projection mapping, which sends the law $P$ of a random vector $\mathbf R$ to the law of $\mathbf r = x'\mathbf R$. Then
--
--   1. the mapping sends $\mathbb{M}^n_{(\mu,\Sigma)}$ into $\mathbb{M}_{(\mu_x,\sigma_x^2)}$, and
--   2. it is onto: every law in $\mathbb{M}_{(\mu_x,\sigma_x^2)}$ is the law of $x'\mathbf R$ for some $\mathbf R\sim(\mu,\Sigma)$.
--
--   Equivalently,
--
--   $$
--   \bigl\{\, P\circ (R\mapsto x'R)^{-1} \;:\; P\in\mathbb{M}^n_{(\mu,\Sigma)} \bigr\} = \mathbb{M}_{(x'\mu,\; x'\Sigma x)} .
--   $$
--
--   As a consequence, for any objective $u$, the robust objective $\min_{\mathbf R\sim(\mu,\Sigma)}E[u(x'\mathbf R)]$ equals the univariate problem $\min_{\mathbf r\sim(\mu_x,\sigma_x^2)}E[u(\mathbf r)]$ (Proposition 1 of the paper), so robust mean-covariance problems reduce to bicriteria problems in $(\mu_x,\sigma_x)$.
--
--   **Formalization Note** Laws are Borel probability measures on `EuclideanSpace ℝ (Fin n)` and on $\mathbb{R}$, with finite second moments; the projection acts by pushforward under the continuous map $R\mapsto\langle x,R\rangle$. The statement is the conjunction `Set.MapsTo ∧ Set.SurjOn` with both source and target classes explicit. The degenerate case $x'\Sigma x = 0$ is included. No bound on $n$ is assumed; $x\neq 0$ forces $n\ge 1$.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, https://doi.org/10.1287/opre.1060.0353, p. 100, §2.1, Theorem 1 (General Projection Property)

import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

/-- Theorem 1 (General Projection Property), Popescu 2007, §2.1, p. 100: for `Σ ⪰ 0` and
`x ≠ 0`, the projection `R ↦ x′R` maps `𝕄ⁿ_(μ,Σ)` into and onto `𝕄_(x′μ, x′Σx)`. -/
theorem general_projection_property {n : ℕ} (μ x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) (hx : x ≠ 0) :
    Set.MapsTo (fun P : Measure (EuclideanSpace ℝ (Fin n)) => P.map (fun R => ⟪x, R⟫))
        (MeanCovClass μ S) (RobustMeanCov.Shared.MeanVarClass ⟪x, μ⟫ (x.ofLp ⬝ᵥ S *ᵥ x.ofLp)) ∧
      Set.SurjOn (fun P : Measure (EuclideanSpace ℝ (Fin n)) => P.map (fun R => ⟪x, R⟫))
        (MeanCovClass μ S) (RobustMeanCov.Shared.MeanVarClass ⟪x, μ⟫ (x.ofLp ⬝ᵥ S *ᵥ x.ofLp)) := by sorry

end RobustMeanCov.Projection
