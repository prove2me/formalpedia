-- Prove2me | Theorems.Thm_TokenFinance_Statics_eq_46
-- name    : TokenFinance.Statics.eq_46
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:42.249581+00:00
-- url     : https://prove2.me/theorems/28b23644-7c73-4281-9ed0-67f5f6b93567
-- title:
--   Equation (46), p. 42 — the break-even residual decreases in demand
-- statement:
--   Fix marginal cost $c>0$, pre-sale size $t>0$, and set-up cost $C_0$. When $c+2t<\theta$, the partial derivative of the break-even residual with respect to the demand upper endpoint is
--   $$\frac{\partial F}{\partial\theta}=\frac{c}{3}\frac{((\theta-c)/2-t)^2(2\theta+c+2t)}{(c+t)\theta^2}-\frac{(\theta-c)^2(2\theta+c)}{12\theta^2}<0.$$
--   This is the demand-direction sign used in Proposition 4.
--
--   **Formalization Note** The condition $c+2t<\theta$ places the pre-sale below the maximal monopoly quantity and ensures $\theta>0$.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 42 (PDF p. 43), Appendix A, proof of Proposition 4, (46)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.Statics

theorem eq_46 (c C0 θ t : ℝ) (hc : 0 < c) (ht : 0 < t)
    (hregion : c + 2 * t < θ) :
    HasDerivAt
        (fun T : ℝ => c / (c + t) * (2 / (3 * T)) * ((T - c) / 2 - t) ^ 3 -
          (T - c) ^ 3 / (12 * T) + C0)
        (c / 3 * ((θ - c) / 2 - t) ^ 2 * (2 * θ + c + 2 * t) /
            ((c + t) * θ ^ 2) -
          (θ - c) ^ 2 * (2 * θ + c) / (12 * θ ^ 2)) θ ∧
      (c / 3 * ((θ - c) / 2 - t) ^ 2 * (2 * θ + c + 2 * t) /
            ((c + t) * θ ^ 2) -
          (θ - c) ^ 2 * (2 * θ + c) / (12 * θ ^ 2)) < 0 := by sorry

end TokenFinance.Statics
