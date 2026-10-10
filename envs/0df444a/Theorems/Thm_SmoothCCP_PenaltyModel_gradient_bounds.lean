-- Prove2me | Theorems.Thm_SmoothCCP_PenaltyModel_gradient_bounds
-- name    : SmoothCCP.PenaltyModel.gradient_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:28.513076+00:00
-- url     : https://prove2.me/theorems/c142fb5c-e2fd-4e34-b18b-488e33ca2bae
-- title:
--   Proof of Proposition 4.1, p. 15 — Σⱼ Γ′_ε(zⱼ − Q_ε(z)) ≤ −κ < 0 uniformly in z, and 0 ≤ [∇Q_ε(z)]ᵢ ≤ 1
-- statement:
--   Let $\varepsilon>0$, let $\Gamma_\varepsilon$ be built from the quartic kernel (2.6), let $0<\alpha<1$, $N\ge1$ and $(1-\alpha)N\notin\mathbb Z$, and let $Q_\varepsilon$ be the smoothed $(1-\alpha)$-quantile of (2.3). Then:
--   1. the denominator of the gradient formula is bounded away from zero uniformly in $z$: there is $\kappa>0$ such that
--   $$
--   \sum_{j=1}^N\Gamma_\varepsilon'(z_j-Q_\varepsilon(z))\le-\kappa\qquad\text{for all }z\in\mathbb R^N;
--   $$
--   2. for all $z\in\mathbb R^N$ and all $i$,
--   $$
--   0\le\frac{\Gamma_\varepsilon'(z_i-Q_\varepsilon(z))}{\sum_{j=1}^N\Gamma_\varepsilon'(z_j-Q_\varepsilon(z))}\le1 .
--   $$
--
--   Since $\Gamma_\varepsilon$ is nonincreasing, the denominator is nonpositive, so "bounded away from zero" means bounded above by a fixed negative number. Combined with the gradient formula, item 2 says $0\le[\nabla Q_\varepsilon(z)]_i\le1$, so $Q_\varepsilon$ is nondecreasing in each coordinate and has bounded gradient.
--
--   **Formalization Note** The constant $\kappa$ is quantified before $z$, so the bound is uniform, as the paper claims ("for all $z\in\mathbb R^N$"). $\Gamma_\varepsilon'$ is `deriv` of the smoothed indicator.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, proof of Proposition 4.1, p. 15, second and third paragraphs

import Mathlib
import Definitions.Def_SmoothCCP_PenaltyModel_Setting

namespace SmoothCCP.PenaltyModel

/-- Proof of Proposition 4.1, arXiv:1905.07377v2, p. 15: with γ_ε the quartic kernel (2.6) and
(1 − α)N ∉ ℤ, the denominator Σⱼ Γ′_ε(zⱼ − Q_ε(z)) is bounded away from zero uniformly in z (it is
nonpositive, so it is at most −κ for a fixed κ > 0), and every ratio
Γ′_ε(zᵢ − Q_ε(z)) / Σⱼ Γ′_ε(zⱼ − Q_ε(z)) lies in [0, 1]. -/
theorem gradient_bounds {N : ℕ} (ε α : ℝ) (hε : 0 < ε) (hα0 : 0 < α) (hα1 : α < 1)
    (hN : 1 ≤ N) (hαN : ∀ k : ℤ, (1 - α) * N ≠ k) :
    (∃ κ : ℝ, 0 < κ ∧ ∀ z : Fin N → ℝ,
        ∑ j : Fin N, deriv (SmoothCCP.Feasibility.Gam ε (quarticGamma ε)) (z j - smoothQuantile ε (quarticGamma ε) α z)
          ≤ -κ) ∧
      ∀ (z : Fin N → ℝ) (i : Fin N),
        0 ≤ deriv (SmoothCCP.Feasibility.Gam ε (quarticGamma ε)) (z i - smoothQuantile ε (quarticGamma ε) α z) /
            ∑ j : Fin N, deriv (SmoothCCP.Feasibility.Gam ε (quarticGamma ε)) (z j - smoothQuantile ε (quarticGamma ε) α z) ∧
        deriv (SmoothCCP.Feasibility.Gam ε (quarticGamma ε)) (z i - smoothQuantile ε (quarticGamma ε) α z) /
            ∑ j : Fin N, deriv (SmoothCCP.Feasibility.Gam ε (quarticGamma ε)) (z j - smoothQuantile ε (quarticGamma ε) α z)
          ≤ 1 := by sorry

end SmoothCCP.PenaltyModel
