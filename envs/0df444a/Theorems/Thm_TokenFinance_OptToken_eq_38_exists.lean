-- Prove2me | Theorems.Thm_TokenFinance_OptToken_eq_38_exists
-- name    : TokenFinance.OptToken.eq_38_exists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:21.999313+00:00
-- url     : https://prove2.me/theorems/932ad3b7-6d88-4aa3-be14-1377982f64f8
-- title:
--   Equation (38): existence of an interior break-even pre-sale size
-- statement:
--   Suppose $0<c<\theta$, the set-up cost $C_0$ is positive, and the project's NPV $V=E_\theta[\pi^m]-C_0$ is positive. Then the contract equation (16) has a solution strictly between zero and the largest monopoly output:
--
--   $$\exists t\in\left(0,\frac{\theta-c}{2}\right):\quad\frac{c}{c+t}\frac{2}{3\theta}\left(\frac{\theta-c}{2}-t\right)^3=\frac{(\theta-c)^3}{12\theta}-C_0.$$
--
--   This gives an economically admissible pre-sale size. The endpoints correspond to a shortfall of $C_0$ and to positive NPV, respectively.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), pp. 40–41 (PDF pp. 41–42), (38) and following paragraph

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.OptToken

theorem eq_38_exists (c C0 θ : ℝ) (hc : 0 < c) (hcθ : c < θ)
    (hC0 : 0 < C0) (hnpv : 0 < TokenFinance.Debt.npv c C0 θ) :
    ∃ t : ℝ, 0 < t ∧ t < (θ - c) / 2 ∧ TokenFinance.Debt.tokenBreakEven c C0 θ t := by sorry

end TokenFinance.OptToken
