-- Prove2me | Theorems.Thm_UtilityTokens_ICOChoice_reduced_ico_problem
-- name    : UtilityTokens.ICOChoice.reduced_ico_problem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:09.07796+00:00
-- url     : https://prove2.me/theorems/f00008df-eb0d-42fb-a237-25a8b6760349
-- title:
--   §5.2, pp. 21–22 — the ICO problem reduces to an attained maximum over θ̄ ∈ [1, Θ]
-- statement:
--   Let $\Theta>1$, $x>0$ and $f\in\mathbb R$. For every threshold $\bar\theta\in[1,\Theta]$, the ICO profit at the late price $p^I_1=v$ equals
--   $$X_I(\bar\theta,v)=\Bigl[\frac{\Theta-\bar\theta}{\Theta}\,x\Bigr]\Bigl[\frac{\Theta-\bar\theta}{\Theta}(\bar\theta-1)+1\Bigr]-f .$$
--
--   For $\bar\theta>1$ this is display (13); at $\bar\theta=1$ it is display (14). That one formula covers both cases is the paper's "no discontinuity in entrepreneurial profits around $p^I_0=v$". The maximum of this expression on $[1,\Theta]$ is attained and equals the optimal ICO payoff $X_I^*$ from the original two-price problem (10).
-- source:
--   Shakhnov & Zaccaria, Utility Tokens, Network Effects, and Pricing Power, SSRN working paper 3613261 (PDF of 2023-04-23), pp. 21–22, §5.2, displays (13), (14) and the reduced problem

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting

namespace UtilityTokens.ICOChoice

theorem reduced_ico_problem (Θ x f : ℝ) (hΘ1 : 1 < Θ) (hx : 0 < x) :
    let g : ℝ → ℝ := fun θbar =>
      (Θ - θbar) / Θ * x * ((Θ - θbar) / Θ * (θbar - 1) + 1) - f
    (∀ θbar ∈ Set.Icc 1 Θ,
      profitI Θ x f θbar (basicUtility Θ x θbar) = g θbar) ∧
    IsGreatest (g '' Set.Icc 1 Θ) (optPayoffI Θ x f) := by sorry

end UtilityTokens.ICOChoice
