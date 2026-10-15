-- Prove2me | Theorems.Thm_Plasticity_CUB37
-- name    : Plasticity.CUB37
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T08:54:05.248113+00:00
-- url     : https://prove2.me/theorems/989196da-7d93-4d14-b108-36e4511c071d
-- title:
--   Nonexpansive bijections between balls of spaces between $c_{00}$ and $c_0$ are signed coordinate bijections
-- statement:
--   Let $\Gamma,\Delta$ be sets, $X$ a space between $c_{00}(\Gamma)$ and $c_0(\Gamma)$ and $Y$ a space between $c_{00}(\Delta)$ and $c_0(\Delta)$, both with the supremum norm, and let $F\colon B_X\to B_Y$ be a nonexpansive bijection of their closed unit balls.
--   Suppose that $X=c_{00}(\Gamma)$, or that $Y$ realizes all sign patterns (for instance $Y=c_0(\Delta)$).
--   Then there are a bijection $\sigma\colon\Gamma\to\Delta$ and signs $\alpha_n\in\{1,-1\}$ such that
--   $$F(x)_{\sigma(n)}=\alpha_n x_n\qquad\text{for all }x\in B_X,\ n\in\Gamma;$$
--   that is, $F$ is the restriction of a signed coordinate bijection.
--   No continuity of $F^{-1}$ is assumed.
-- source:
--   This repository: claim CUB37 (claims/cub.md), item (iii), in the form of Corollary 4 (i)–(ii) of expositions/c0_between_spaces.md; proof in §§2–4 there

import Definitions.Def_Plasticity_SeqSpace
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity
theorem CUB37 {Γ Δ : Type*} (X : Submodule ℝ (Linf Γ)) (Y : Submodule ℝ (Linf Δ))
    (hX0 : c00 Γ ≤ X) (hX1 : X ≤ c0 Γ) (hY0 : c00 Δ ≤ Y) (hY1 : Y ≤ c0 Δ)
    (hmatch : X = c00 Γ ∨ RealizesSignPatterns Y)
    (F : Linf Γ → Linf Δ)
    (hbij : Set.BijOn F (ballIn X) (ballIn Y))
    (hlip : LipschitzOnWith 1 F (ballIn X)) :
    ∃ σ : Γ ≃ Δ, ∃ α : Γ → ℝ, (∀ n, α n = 1 ∨ α n = -1) ∧
      ∀ x ∈ ballIn X, ∀ n, F x (σ n) = α n * x n := by sorry
end Plasticity
