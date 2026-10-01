-- Prove2me | Theorems.Thm_VeinottWagnerSS_Bounds_SLow_characterization
-- name    : VeinottWagnerSS.Bounds.SLow_characterization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T13:36:05.088466+00:00
-- url     : https://prove2.me/theorems/39d520aa-baf0-4a44-a113-678aa5a0ed56
-- title:
--   §4, p. 537 — $\underline{S}$ exists and is the unique integer with $\Delta G_\alpha(\underline{S}-1) < 0 \le \Delta G_\alpha(\underline{S})$
-- statement:
--   Let $G_\alpha : \mathbb Z \to \mathbb R$ be convex on the integers, i.e. its forward differences $\Delta G_\alpha(y) = G_\alpha(y+1) - G_\alpha(y)$ are non-decreasing in $y$, and suppose $G_\alpha(y) \to \infty$ as $y \to +\infty$ and as $y \to -\infty$. Let $K \ge 0$ and $0 \le \alpha \le 1$. Then the set of integers minimizing $G_\alpha$ has a least element, namely $\underline{S}$, and an integer $y$ satisfies
--   $$\Delta G_\alpha(y - 1) < 0 \le \Delta G_\alpha(y)$$
--   if and only if $y = \underline{S}$.
--
--   This is the characterization of $\underline{S}$ given on p. 537 of Veinott and Wagner (1965); it identifies the order-up-to level of the single-period problem and is the anchor of all four bounds (21)–(23).
--
--   **Formalization Note** The hypotheses on $K$ and $\alpha$ are the paper's standing assumptions and are not used by this statement. $\Delta G_\alpha(y-1)$ is written `G y - G (y - 1)`.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 537, Section 4 'Bounds on s* and S*', definition of S underbar and display ΔG_α(S̲ − 1) < 0 ≤ ΔG_α(S̲)

import Mathlib
import Definitions.Def_VeinottWagnerSS_Bounds_CriticalNumbers

namespace VeinottWagnerSS.Bounds

/-- p. 537: under the standing assumptions (`G_α` convex on `ℤ` and `G_α(y) → ∞` as
`|y| → ∞`), `S̲ = SLow G` is the smallest integer minimizing `G_α`, and it is the unique
integer `y` with `ΔG_α(y − 1) < 0 ≤ ΔG_α(y)`, where `ΔG_α(y) = G_α(y + 1) − G_α(y)`. -/
theorem SLow_characterization (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop) :
    IsLeast {y : ℤ | ∀ z : ℤ, G y ≤ G z} (SLow G) ∧
      ∀ y : ℤ, (G y - G (y - 1) < 0 ∧ 0 ≤ G (y + 1) - G y ↔ y = SLow G) := by sorry

end VeinottWagnerSS.Bounds
