-- Prove2me | Theorems.Thm_TokenFinance_Statics_eq_45
-- name    : TokenFinance.Statics.eq_45
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:34.196327+00:00
-- url     : https://prove2.me/theorems/5c8a4f1c-d4b0-482f-b8ca-cbbf642ffd75
-- title:
--   Equation (45), p. 42 — the break-even residual increases in marginal cost
-- statement:
--   Fix a positive pre-sale size $t$, demand upper endpoint $\theta>0$, and set-up cost $C_0$. For $0<c<\theta-2t$, the partial derivative of the break-even residual with respect to marginal cost is
--   $$\frac{\partial F}{\partial c}=\frac{2t}{3}\frac{((\theta-c)/2-t)^3}{(c+t)^2\theta}+\left(\frac{(\theta-c)^2}{4\theta}-\frac{c((\theta-c)/2-t)^2}{(c+t)\theta}\right)>0.$$
--   This gives the cost-direction sign used in Proposition 4.
--
--   **Formalization Note** The final denominator is $(c+t)\theta$, correcting the printed $(c+t)^2\theta$. The printed claim that the parenthesized expression vanishes at $t=0$ confirms this correction.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 42 (PDF p. 43), Appendix A, proof of Proposition 4, (45), corrected final denominator

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.Statics

theorem eq_45 (c C0 θ t : ℝ) (hc : 0 < c) (hθ : 0 < θ) (ht : 0 < t)
    (hregion : c < θ - 2 * t) :
    HasDerivAt
        (fun d : ℝ => d / (d + t) * (2 / (3 * θ)) * ((θ - d) / 2 - t) ^ 3 -
          (θ - d) ^ 3 / (12 * θ) + C0)
        (2 * t / 3 * ((θ - c) / 2 - t) ^ 3 / ((c + t) ^ 2 * θ) +
          ((θ - c) ^ 2 / (4 * θ) -
            c * ((θ - c) / 2 - t) ^ 2 / ((c + t) * θ))) c ∧
      0 < (2 * t / 3 * ((θ - c) / 2 - t) ^ 3 / ((c + t) ^ 2 * θ) +
          ((θ - c) ^ 2 / (4 * θ) -
            c * ((θ - c) / 2 - t) ^ 2 / ((c + t) * θ))) := by sorry

end TokenFinance.Statics
