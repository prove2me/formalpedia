-- Prove2me | Theorems.Thm_TokenFinance_OptToken_eq_3
-- name    : TokenFinance.OptToken.eq_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:24.554129+00:00
-- url     : https://prove2.me/theorems/e3b5ca3b-d637-4d26-9d25-b538fa0c58e9
-- title:
--   Equation (3): closed form for the project's NPV
-- statement:
--   Suppose the marginal cost $c$ is positive, the upper demand intercept $\theta$ exceeds $c$, and the set-up cost is $C_0$. With monopoly operating profit $\pi^m(x)=\max\{x-c,0\}^2/4$ and $x$ uniform on $(0,\theta)$,
--
--   $$E_\theta[\pi^m]-C_0=\frac{(\theta-c)^3}{12\theta}-C_0.$$
--
--   This evaluates the project's NPV from its realized monopoly profit and supplies the boundary values used in the token break-even argument.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 14 (PDF p. 15), (3)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.OptToken

theorem eq_3 (c C0 θ : ℝ) (hc : 0 < c) (hcθ : c < θ) :
    TokenFinance.Debt.npv c C0 θ = (θ - c) ^ 3 / (12 * θ) - C0 := by sorry

end TokenFinance.OptToken
