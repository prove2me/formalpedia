-- Prove2me | Theorems.Thm_RobustMultitask_Estimator_eq_19_lasso_cone
-- name    : RobustMultitask.Estimator.eq_19_lasso_cone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:34:26.41798+00:00
-- url     : https://prove2.me/theorems/8df9fbd9-c971-47cb-84e2-6cb3b7f84f86
-- title:
--   (19), p. 42 — on ℋʲ: (1/nⱼ)‖Xʲ(β̂ − βʲ)‖₂² + (λⱼ/2)‖β̂ − βʲ‖₁ ≤ 2λⱼ‖(β̂ − βʲ)_{ℐ̄ⱼ}‖₁ + 2λⱼ‖(β̂† − β†)_{ℐ_poor}‖₁
-- statement:
--   Let $\beta^1,\dots,\beta^N,\beta^\dagger\in\mathbb R^d$ and $\zeta\in\mathbb R$, and fix a task $j$. Let $X\in\mathbb R^{m\times d}$, $m\ge 1$, be the design of task $j$, and let its responses be $Y=X\beta^j+e$ for a noise vector $e\in\mathbb R^m$ in the event $\mathcal H^j$ of (15):
--   $$\frac{2}{m}\|X^\top e\|_\infty\le\frac{\lambda_j}{2}.$$
--   Let $b\in\mathbb R^d$ be any centre (in Algorithm 1, $b=\widehat\beta^\dagger_{\mathrm{RM}}$), and let $\widehat\beta$ be a global minimizer of $\beta\mapsto\frac1m\|X\beta-Y\|_2^2+\lambda_j\|\beta-b\|_1$ (in Algorithm 1, $\widehat\beta=\widehat\beta^j_{\mathrm{RM}}$). Then
--   $$\frac{1}{m}\|X(\widehat\beta-\beta^j)\|_2^2+\frac{\lambda_j}{2}\|\widehat\beta-\beta^j\|_1\ \le\ 2\lambda_j\big\|(\widehat\beta-\beta^j)_{\bar{\mathcal I}_j}\big\|_1+2\lambda_j\big\|(b-\beta^\dagger)_{\mathcal I_{\mathrm{poor}}}\big\|_1,$$
--   where $\bar{\mathcal I}_j=\mathcal I^\zeta_{\mathrm{well}}\cup\mathcal I_j$ and $\mathcal I_{\mathrm{poor}}=\mathcal I^\zeta_{\mathrm{poor}}$ are computed from $\{\beta^k\}$ and $\beta^\dagger$ (Definition 2).
--
--   This is the cone inequality of the LASSO step: the estimation error is controlled by its part on the small set $\bar{\mathcal I}_j$ plus the error of the shared estimate on the poorly-aligned components.
--
--   **Formalization Note** The statement is deterministic: it holds pointwise on $\mathcal H^j$. The centre $b$ is arbitrary; the paper's (19) is the case $b=\widehat\beta^\dagger_{\mathrm{RM}}$, $m=n_j$, $e=\epsilon^j$, and its proof uses no property of $\widehat\beta^\dagger_{\mathrm{RM}}$. No sparsity, Assumption 1 or range of $\zeta$ is needed for (19).
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 42, eq. (19)

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_Algorithm
import Definitions.Def_RobustMultitask_Estimator_Alignment

namespace RobustMultitask.Estimator

open Matrix

/-- Equation (19), p. 42, on the event `ℋʲ` of (15). Let `X ∈ ℝ^{m×d}` (`m ≥ 1`) be the design
of task `j`, `Y = Xβʲ + e` its responses with a noise vector `e` satisfying
`(2/m) ‖Xᵀe‖_∞ ≤ λ_j/2`, and let `β̂` minimize `(1/m)‖Xβ − Y‖₂² + λ_j‖β − b‖₁` for a centre
`b ∈ ℝᵈ` (in Algorithm 1, `b = β̂†_RM`). Then
`(1/m)‖X(β̂ − βʲ)‖₂² + (λ_j/2)‖β̂ − βʲ‖₁ ≤ 2λ_j‖(β̂ − βʲ)_{ℐ̄ⱼ}‖₁ + 2λ_j‖(b − β†)_{ℐ_poor}‖₁`,
with `ℐ̄ⱼ = ℐ^ζ_well ∪ ℐⱼ` and `ℐ_poor = ℐ^ζ_poor` computed from the family `{βᵏ}` and `β†`. -/
theorem eq_19_lasso_cone {N d m : ℕ} (X : Matrix (Fin m) (Fin d) ℝ)
    (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ) (ζ : ℝ) (j : Fin N) (lam : ℝ)
    (e : Fin m → ℝ) (b βhat : Fin d → ℝ) (hm : 0 < m)
    (hH : (2 / (m : ℝ)) * linf (Xᵀ *ᵥ e) ≤ lam / 2)
    (hmin : IsLassoMinimizer X (X *ᵥ β j + e) lam b βhat) :
    (1 / (m : ℝ)) * l2sq (X *ᵥ (βhat - β j)) + lam / 2 * l1 (βhat - β j)
      ≤ 2 * lam * l1 (restrict (augSupport β βdag ζ j) (βhat - β j))
        + 2 * lam * l1 (restrict (poorlyAligned β βdag ζ) (b - βdag)) := by sorry

end RobustMultitask.Estimator
