-- Prove2me | Theorems.Thm_UnifiedMEstimator_General_theorem1_general_bound
-- name    : UnifiedMEstimator.General.theorem1_general_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:13:47.803925+00:00
-- url     : https://prove2.me/theorems/7bcda162-290c-48f6-99a4-05c6189b5eba
-- title:
--   Theorem 1 — Bounds for general models (tolerance term corrected)
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with norm $\|\cdot\|$, let $\mathcal L:E\to\mathbb R$ be a loss and $\mathcal R:E\to\mathbb R$ a regularizer, and consider the regularized M-estimator (program (1))
--   $$\hat\theta_{\lambda_n}\in\arg\min_{\theta\in E}\bigl\{\mathcal L(\theta)+\lambda_n\mathcal R(\theta)\bigr\}.$$
--   Assume
--
--   1. **(G1)** $\mathcal R$ is a norm and is decomposable with respect to $(\mathcal M,\overline{\mathcal M}^\perp)$, where $\mathcal M\subseteq\overline{\mathcal M}$;
--   2. **(G2)** $\mathcal L$ is convex and differentiable, and satisfies restricted strong convexity at $\theta^*\in E$ with curvature $\kappa_{\mathcal L}>0$ and tolerance $\tau_{\mathcal L}(\theta^*)$: $\delta\mathcal L(\Delta,\theta^*)\ge\kappa_{\mathcal L}\|\Delta\|^2-\tau_{\mathcal L}^2(\theta^*)$ for all $\Delta\in\mathbb C(\mathcal M,\overline{\mathcal M}^\perp;\theta^*)$;
--   3. the regularization constant satisfies $\lambda_n>0$ and $\lambda_n\ge2\,\mathcal R^*(\nabla\mathcal L(\theta^*))$, where $\mathcal R^*$ is the dual norm.
--
--   Then every optimal solution $\hat\theta_{\lambda_n}$ of program (1) satisfies
--
--   $$
--   \|\hat\theta_{\lambda_n}-\theta^*\|^2\le 9\,\frac{\lambda_n^2}{\kappa_{\mathcal L}^2}\,\Psi^2(\overline{\mathcal M})+\frac{2\tau_{\mathcal L}^2(\theta^*)+4\lambda_n\,\mathcal R(\theta^*_{\mathcal M^\perp})}{\kappa_{\mathcal L}},
--   $$
--
--   where $\Psi$ is the subspace compatibility constant and $\theta^*_{\mathcal M^\perp}$ the orthogonal projection of $\theta^*$ onto $\mathcal M^\perp$.
--
--   **Correction of the printed statement.** Display (22) prints the tolerance term as $\frac{\lambda_n}{\kappa_{\mathcal L}}\cdot2\tau_{\mathcal L}^2(\theta^*)$; we state $2\tau_{\mathcal L}^2(\theta^*)/\kappa_{\mathcal L}$, since the printed form fails for $E=\mathbb R$, $\mathcal R=|\cdot|$, $\mathcal M=\overline{\mathcal M}=\mathbb R$, $\mathcal L(\theta)=(\max(0,|\theta|-1))^2$, $\theta^*=0.9$, $\lambda_n=0.01$, $\kappa_{\mathcal L}=1/2$, $\tau^2_{\mathcal L}=10$: then $\hat\theta=0$ and $\|\hat\theta-\theta^*\|^2=0.81$, while the printed right-hand side is $0.4036$. The two forms coincide when $\tau_{\mathcal L}(\theta^*)=0$; the constants $9$ and $4$ are the paper's.
--
--   Theorem 1 is the paper's main result: a deterministic bound, holding for any optimum of the convex program, that splits into an estimation error $9\lambda_n^2\Psi^2(\overline{\mathcal M})/\kappa_{\mathcal L}^2$ and an approximation error driven by $\mathcal R(\theta^*_{\mathcal M^\perp})$. Specialised to particular losses and regularizers it gives the Lasso, group-Lasso and nuclear-norm rates.
--
--   **Formalization Note** $\theta^*$ is an arbitrary point of $E$: the theorem is deterministic (Remark (a), p. 10) and uses no property of $\theta^*$ beyond the stated hypotheses, so the paper's requirement that $\theta^*$ minimise the population risk is dropped (a generalisation). $\tau_{\mathcal L}(\theta^*)$ is a real number $\tau$ entering as $\tau^2$; $\kappa_{\mathcal L}>0$ is part of the RSC predicate. The dual norm and $\Psi$ are real suprema, equal to the paper's because $\mathcal R$ is a norm on a finite-dimensional space. The gradient is Mathlib's `gradient`, meaningful because $\mathcal L$ is assumed differentiable.
-- source:
--   Negahban, Ravikumar, Wainwright and Yu, A Unified Framework for High-Dimensional Analysis of M-Estimators with Decomposable Regularizers, arXiv:1010.2731v3, p. 10, Theorem 1, Eq. (22), with conditions (G1), (G2) (p. 10)

import Mathlib
import Definitions.Def_UnifiedMEstimator_General_Core

namespace UnifiedMEstimator.General

/-- Theorem 1 (Bounds for general models), p. 10, display (22), with the tolerance term
corrected from the printed `(λ/κ)·2τ²` to `2τ²/κ` (the printed form is false; see the
natural-language statement). Under (G1) — `R` a norm, decomposable with respect to
`(M, M̄⊥)` with `M ⊆ M̄` — and (G2) — `L` convex, differentiable and RSC with curvature `κ`
and tolerance `τ` over `C(M, M̄⊥; θ*)` — for every `λ > 0` with `λ ≥ 2R*(∇L(θ*))`, every
optimal solution `θhat` of program (1) satisfies
`‖θhat − θ*‖² ≤ 9 λ²/κ² Ψ²(M̄) + (2τ² + 4λR(θ*_{M⊥}))/κ`. -/
theorem theorem1_general_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L R : E → ℝ) (M Mbar : Submodule ℝ E) (θstar θhat : E) (lam κ τ : ℝ)
    (hR : IsNormFn R) (hdec : IsDecomposable R M Mbar)
    (hconv : ConvexOn ℝ Set.univ L) (hdiff : Differentiable ℝ L)
    (hRSC : RSC L R M Mbar θstar κ τ)
    (hlam : 0 < lam) (hlam_dual : 2 * dualNorm R (gradient L θstar) ≤ lam)
    (hopt : IsOptimal L R lam θhat) :
    ‖θhat - θstar‖ ^ 2 ≤ 9 * lam ^ 2 / κ ^ 2 * compat R Mbar ^ 2
        + (2 * τ ^ 2 + 4 * lam * R (Mᗮ.starProjection θstar)) / κ := by sorry

end UnifiedMEstimator.General
