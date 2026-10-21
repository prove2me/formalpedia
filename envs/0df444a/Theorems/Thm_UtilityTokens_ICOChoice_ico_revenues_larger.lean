-- Prove2me | Theorems.Thm_UtilityTokens_ICOChoice_ico_revenues_larger
-- name    : UtilityTokens.ICOChoice.ico_revenues_larger
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:24.757997+00:00
-- url     : https://prove2.me/theorems/3c3225d1-bb68-4cc3-b1a3-b136ca87d91b
-- title:
--   Section 6, p. 23 — for Θ ∈ (Θ̃, 3] ICO revenues strictly exceed traditional-sales revenues, and X*_I − X*_T = F(Θ)x − f
-- statement:
--   Let $\tilde\Theta=(\sqrt5+3)/2$, $\Theta\in(\tilde\Theta,3]$, $x>0$ and $f\in\mathbb R$, and let
--   $$F(\Theta)=(\theta^*-1)\Bigl[\Bigl(\frac{\Theta-\theta^*}{\Theta}\Bigr)^2-\frac1\Theta\Bigr]$$
--   with $\theta^*$ from (11). Then:
--
--   1. the ICO revenues exceed the traditional-sales revenues, $X^*_T<X^*_I+f$;
--   2. $F(\Theta)>0$;
--   3. $X^*_I-X^*_T=F(\Theta)\,x-f$.
--
--   The identity is what produces the threshold $\bar x=f/F(\Theta)$ of (16), and the positivity of $F$ is what makes that threshold positive.
--
--   **Formalization Note** Appendix A takes $\bigl((\Theta-\theta^*)/\Theta\bigr)^2-1/\Theta>0$ from "$f>0$ and $\bar x>0$", which presupposes the sign of $\bar x$; here the positivity of $F$ is stated on its own.
-- source:
--   Shakhnov & Zaccaria, Utility Tokens, Network Effects, and Pricing Power, SSRN working paper 3613261 (PDF of 2023-04-23), p. 23, Section 6

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting

namespace UtilityTokens.ICOChoice

theorem ico_revenues_larger (Θ x f : ℝ) (hΘ : thetaTilde < Θ) (hΘ3 : Θ ≤ 3)
    (hx : 0 < x) :
    optPayoffT Θ x < optPayoffI Θ x f + f ∧
    0 < Fden Θ ∧
    optPayoffI Θ x f - optPayoffT Θ x = Fden Θ * x - f := by sorry

end UtilityTokens.ICOChoice
