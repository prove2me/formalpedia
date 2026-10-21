-- Prove2me | Theorems.Thm_UtilityTokens_ICOChoice_optimal_late_price
-- name    : UtilityTokens.ICOChoice.optimal_late_price
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:19.81259+00:00
-- url     : https://prove2.me/theorems/81550623-bb0d-44f0-a30c-fb4dc71f9174
-- title:
--   §5.2, p. 21 — in the ICO the late price p₁ᴵ = v is optimal for every threshold
-- statement:
--   Let $\Theta>1$, $x>0$ and $f\in\mathbb R$. Fix an ICO threshold $\bar\theta\in[1,\Theta]$, so that the token price is $p^I_0=\bar\theta v$ with $v=\frac{\Theta-\bar\theta}{\Theta}x$. For every late price $p^I_1\in[v,\Theta v]$,
--   $$X_I(\bar\theta,p^I_1)\le X_I(\bar\theta,v).$$
--
--   Late buyers cannot become active, so they pay at most the basic user's reservation value; the statement reduces the two-price problem (10) to a choice of $\bar\theta$ alone.
-- source:
--   Shakhnov & Zaccaria, Utility Tokens, Network Effects, and Pricing Power, SSRN working paper 3613261 (PDF of 2023-04-23), p. 21, §5.2, proof of Proposition 2

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting

namespace UtilityTokens.ICOChoice

theorem optimal_late_price (Θ x f : ℝ) (hΘ1 : 1 < Θ) (hx : 0 < x) :
    ∀ θbar ∈ Set.Icc 1 Θ,
      ∀ p1 ∈ Set.Icc (basicUtility Θ x θbar) (Θ * basicUtility Θ x θbar),
        profitI Θ x f θbar p1 ≤ profitI Θ x f θbar (basicUtility Θ x θbar) := by sorry

end UtilityTokens.ICOChoice
