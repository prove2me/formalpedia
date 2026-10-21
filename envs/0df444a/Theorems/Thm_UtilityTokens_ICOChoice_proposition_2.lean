-- Prove2me | Theorems.Thm_UtilityTokens_ICOChoice_proposition_2
-- name    : UtilityTokens.ICOChoice.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:10.846544+00:00
-- url     : https://prove2.me/theorems/f3c0d442-1326-4fe6-b488-5fecb7bf09a1
-- title:
--   Proposition 2, pp. 20–21 — the ICO optimum uses the threshold θ* of (11), with payoff X*_I of (12)
-- statement:
--   Let $\Theta>1$, $x>0$ and $f\in\mathbb R$, and let
--   $$\theta^*=\max\Bigl[1,\ \frac{2\Theta+1-\sqrt{\Theta^2+\Theta+1}}{3}\Bigr]\qquad(11),$$
--   $$X^*_I=\Bigl[\theta^*\Bigl(\frac{\Theta-\theta^*}{\Theta}\Bigr)^2+\Bigl(1-\frac{\Theta-\theta^*}{\Theta}\Bigr)\frac{\Theta-\theta^*}{\Theta}\Bigr]x-f\qquad(12).$$
--   Then:
--
--   1. $1\le\theta^*\le\Theta$;
--   2. $X^*_I$ is the maximum of the ICO profit over all ICO strategies $(\bar\theta,p^I_1)$;
--   3. it is attained at $\bar\theta=\theta^*$, $p^I_1=v$;
--   4. every maximizing strategy has threshold $\bar\theta=\theta^*$;
--   5. the equilibrium prices are $p^I_0=\theta^*\bigl[\frac{\Theta-\theta^*}{\Theta}x\bigr]$ and $p^I_1=v=\frac{\Theta-\theta^*}{\Theta}x$;
--   6. the optimal ICO payoff equals (12).
--
--   This is the ICO counterpart of Proposition 1.
--
--   **Formalization Note** The proposition holds for every $\Theta>1$ (the paper's Appendix B says it "holds unchanged" for $\Theta>3$), so no upper bound on $\Theta$ is assumed. The late price is not claimed unique: when $\theta^*=1$ no late buyer remains and any $p^I_1$ yields the same profit.
-- source:
--   Shakhnov & Zaccaria, Utility Tokens, Network Effects, and Pricing Power, SSRN working paper 3613261 (PDF of 2023-04-23), pp. 20–21, Proposition 2, displays (10)–(12)

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting

namespace UtilityTokens.ICOChoice

theorem proposition_2 (Θ x f : ℝ) (hΘ1 : 1 < Θ) (hx : 0 < x) :
    let θs := thetaStar Θ
    let XI := (θs * ((Θ - θs) / Θ) ^ 2 + (1 - (Θ - θs) / Θ) * ((Θ - θs) / Θ)) * x - f
    (1 ≤ θs ∧ θs ≤ Θ) ∧
    IsGreatest ((fun c : ℝ × ℝ => profitI Θ x f c.1 c.2) '' ICOChoices Θ x) XI ∧
    profitI Θ x f θs (basicUtility Θ x θs) = XI ∧
    (∀ c ∈ ICOChoices Θ x, profitI Θ x f c.1 c.2 = XI → c.1 = θs) ∧
    (thresholdPrice Θ x θs = θs * ((Θ - θs) / Θ * x) ∧
      basicUtility Θ x θs = (Θ - θs) / Θ * x) ∧
    optPayoffI Θ x f = XI := by sorry

end UtilityTokens.ICOChoice
