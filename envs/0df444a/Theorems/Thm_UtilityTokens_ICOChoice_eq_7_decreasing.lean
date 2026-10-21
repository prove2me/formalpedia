-- Prove2me | Theorems.Thm_UtilityTokens_ICOChoice_eq_7_decreasing
-- name    : UtilityTokens.ICOChoice.eq_7_decreasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:12.395911+00:00
-- url     : https://prove2.me/theorems/bae689dc-6b51-4049-928e-71ae43083104
-- title:
--   §5.1, p. 18 — for Θ ∈ (1, 3] the discriminatory profit (7) decreases in θ̄ and stays below (6)
-- statement:
--   Let $\Theta\in(1,3]$ and $x>0$. For a threshold $\bar\theta\in(1,\Theta]$ the traditional-sales profit is display (7),
--   $$X_T(\bar\theta)=\bar\theta\Bigl(\frac{\Theta-\bar\theta}{\Theta}\Bigr)^2x ,$$
--   this expression is strictly decreasing in $\bar\theta$ on $(1,\Theta]$, and every such profit is strictly smaller than the non-discriminatory profit (6), $X_T(1)=\frac{\Theta-1}{\Theta}x$.
--
--   This is the step that makes non-discriminatory pricing optimal under traditional sales (Proposition 1).
--
--   **Formalization Note** The page writes the discriminatory price range as $(v,\Theta]$; it means $(v,\Theta v]$, as on p. 17, which is what the threshold range $\bar\theta\in(1,\Theta]$ encodes.
-- source:
--   Shakhnov & Zaccaria, Utility Tokens, Network Effects, and Pricing Power, SSRN working paper 3613261 (PDF of 2023-04-23), p. 18, §5.1, display (7) and the paragraph after it

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting

namespace UtilityTokens.ICOChoice

theorem eq_7_decreasing (Θ x : ℝ) (hΘ1 : 1 < Θ) (hΘ3 : Θ ≤ 3) (hx : 0 < x) :
    (∀ θbar ∈ Set.Ioc 1 Θ, profitT Θ x θbar = θbar * ((Θ - θbar) / Θ) ^ 2 * x) ∧
    StrictAntiOn (profitT Θ x) (Set.Ioc 1 Θ) ∧
    ∀ θbar ∈ Set.Ioc 1 Θ, profitT Θ x θbar < profitT Θ x 1 := by sorry

end UtilityTokens.ICOChoice
