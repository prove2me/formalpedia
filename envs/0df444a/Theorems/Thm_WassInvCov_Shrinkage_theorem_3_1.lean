-- Prove2me | Theorems.Thm_WassInvCov_Shrinkage_theorem_3_1
-- name    : WassInvCov.Shrinkage.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:37.678683+00:00
-- url     : https://prove2.me/theorems/b2edfdb9-b414-4145-9c04-e4eb5eb1373e
-- title:
--   Theorem 3.1, p. 12 — without sparsity information the unique minimizer of (5) is X⋆ = Σ x⋆_i v_i v_iᵀ, x⋆_i from (16a) at the positive root γ⋆ of (16b)
-- statement:
--   Let $p\ge1$ and $\rho>0$. Consider the distributionally robust estimation problem (5) without structural information, $\mathcal X=\mathbb S^p_{++}$:
--
--   $$\min_{X\succ0}\ \Big\{-\log\det X+\sup_{\mathbb Q\in\mathcal P^0_\rho}\mathbb E^{\mathbb Q}\big[\langle\xi\xi^\top,X\rangle\big]\Big\},$$
--
--   where $\mathcal P^0_\rho$ is the set of centred normal distributions on $\mathbb R^p$ within type-2 Wasserstein distance $\rho$ of $\mathcal N(0,\widehat\Sigma)$. Let $\widehat\Sigma\in\mathbb S^p_+$ (possibly singular) have the spectral decomposition $\widehat\Sigma=\sum_{i=1}^p\lambda_iv_iv_i^\top$ with orthonormal eigenvectors $v_1,\dots,v_p$. Then:
--   1. the equation
--   $$\Big(\rho^2-\frac12\sum_{i=1}^p\lambda_i\Big)\gamma-p+\frac12\sum_{i=1}^p\sqrt{\lambda_i^2\gamma^2+4\lambda_i\gamma}=0\tag{16b}$$
--   has exactly one positive solution $\gamma^\star$;
--   2. with
--   $$x^\star_i=\gamma^\star\Big[1-\frac12\Big(\sqrt{\lambda_i^2(\gamma^\star)^2+4\lambda_i\gamma^\star}-\lambda_i\gamma^\star\Big)\Big],\qquad i\le p,\tag{16a}$$
--   the matrix $X^\star=\sum_{i=1}^px^\star_iv_iv_i^\top$ is positive definite, attains the minimum of (5) over all positive definite $X$, and every positive definite minimizer of (5) equals $X^\star$.
--
--   The estimator $X^\star$ shares the eigenvectors of $\widehat\Sigma$ and shrinks its eigenvalues by an explicit nonlinear map; it is invertible even when $\widehat\Sigma$ is singular (more dimensions than samples). This is the paper's analytical solution of the robust estimation problem.
--
--   **Formalization Note** The hypothesis $p\ge1$ is added: for $p=0$, (16b) has no positive solution. The eigendecomposition is arbitrary (any orthonormal family $v$ and reals $\lambda$ with $\widehat\Sigma=\sum_i\lambda_iv_iv_i^\top$), so the statement also asserts independence of the choice of eigenbasis. Part 2 is stated for every positive root, which by part 1 is $\gamma^\star$. The objective is the measure-level one of (5), with the worst-case expectation computed as an extended-real supremum over $\mathcal P^0_\rho$; minimality is `IsMinOn` over the positive definite matrices.
-- source:
--   Nguyen, Kuhn & Mohajerin Esfahani, Distributionally Robust Inverse Covariance Estimation, arXiv:1805.07194v1, p. 12, Theorem 3.1, (16a), (16b)

import Mathlib
import Definitions.Def_WassInvCov_Shrinkage_Setting

open MeasureTheory ProbabilityTheory Matrix

namespace WassInvCov.Shrinkage

/-- Theorem 3.1, p. 12 (arXiv:1805.07194v1). Without sparsity information (`𝒳 = 𝕊^p_{++}`), for
`ρ > 0` and `Σ̂ ⪰ 0` with an orthonormal eigendecomposition `Σ̂ = Σᵢ λᵢ vᵢ vᵢᵀ`, equation (16b) has a
unique positive solution `γ⋆`, and `X⋆ = Σᵢ x⋆ᵢ vᵢ vᵢᵀ` with `x⋆ᵢ` from (16a) is the unique minimizer
of (5). The hypothesis `0 < p` is added (for `p = 0`, (16b) has no positive solution). -/
theorem theorem_3_1 {p : ℕ} (hp : 0 < p) (ρ : ℝ) (hρ : 0 < ρ) (Sh : Matrix (Fin p) (Fin p) ℝ)
    (hSh : Sh.PosSemidef) (lam : Fin p → ℝ) (v : Fin p → EuclideanSpace ℝ (Fin p))
    (hv : Orthonormal ℝ v)
    (hdecomp : Sh = ∑ i, lam i • Matrix.vecMulVec (v i).ofLp (v i).ofLp) :
    (∃! γ : ℝ, 0 < γ ∧ phi16b ρ lam γ = 0) ∧
    ∀ γs : ℝ, 0 < γs → phi16b ρ lam γs = 0 →
      (shrinkageEstimator lam v γs).PosDef ∧
      IsMinOn (robustObjective ρ Sh) {X | X.PosDef} (shrinkageEstimator lam v γs) ∧
      ∀ X : Matrix (Fin p) (Fin p) ℝ, X.PosDef →
        IsMinOn (robustObjective ρ Sh) {X | X.PosDef} X → X = shrinkageEstimator lam v γs := by sorry

end WassInvCov.Shrinkage
