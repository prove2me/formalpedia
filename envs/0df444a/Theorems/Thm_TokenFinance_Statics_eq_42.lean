-- Prove2me | Theorems.Thm_TokenFinance_Statics_eq_42
-- name    : TokenFinance.Statics.eq_42
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:32.754388+00:00
-- url     : https://prove2.me/theorems/f220b2a3-7504-411f-af15-f3dfddbc9e29
-- title:
--   Equation (42), p. 41 — the break-even residual decreases in the pre-sale size
-- statement:
--   Fix marginal cost $c>0$, demand upper endpoint $\theta>0$, and set-up cost $C_0$. Let $F(c,C_0,\theta,t)$ be the difference between the two sides of (16). For $0\le t<(\theta-c)/2$, its derivative with respect to $t$ is
--   $$\frac{\partial F}{\partial t}=-\frac{c}{(c+t)^2}\frac{2}{3\theta}\left(\frac{\theta-c}{2}-t\right)^3-\frac{2c}{(c+t)\theta}\left(\frac{\theta-c}{2}-t\right)^2<0.$$
--   This strict sign supplies local monotonicity of the break-even residual at the economically relevant root.
--
--   **Formalization Note** The displayed second term corrects a factor error in printed equation (42). The domain also states $-c<t$ so division by $c+t$ is valid; $0\le t$ already implies it when $c>0$.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 41 (PDF p. 42), Appendix A, proof of Proposition 4, (42), corrected second coefficient

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.Statics

theorem eq_42 (c C0 θ t : ℝ) (hc : 0 < c) (hθ : 0 < θ) (ht : -c < t)
    (hregion : 0 ≤ t ∧ t < (θ - c) / 2) :
    HasDerivAt
        (fun s : ℝ => c / (c + s) * (2 / (3 * θ)) * ((θ - c) / 2 - s) ^ 3 -
          (θ - c) ^ 3 / (12 * θ) + C0)
        (-(c / (c + t) ^ 2) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3 -
          2 * c / ((c + t) * θ) * ((θ - c) / 2 - t) ^ 2) t ∧
      (-(c / (c + t) ^ 2) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3 -
        2 * c / ((c + t) * θ) * ((θ - c) / 2 - t) ^ 2) < 0 := by sorry

end TokenFinance.Statics
