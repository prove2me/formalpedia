-- Prove2me | Theorems.Thm_TokenFinance_OptToken_eq_16_lhs
-- name    : TokenFinance.OptToken.eq_16_lhs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:37.53805+00:00
-- url     : https://prove2.me/theorems/c004fe9a-2b9e-41ae-b74c-406ad3bd42d7
-- title:
--   Equation (16): expected entrepreneur payoff under the token contract
-- statement:
--   Let $c>0$, $t\ge0$, and $c+2t\le\theta$. At the monopoly output $q^m(x)$, the entrepreneur's expected realized token-contract payoff is
--
--   $$E_\theta[\pi_t^e(x,q^m(x))]=\frac{c}{c+t}\frac{2}{3\theta}\left(\frac{\theta-c}{2}-t\right)^3.$$
--
--   This identifies the left-hand side of the contract equation (16) with the entrepreneur's actual expected payment. **Formalization Note** The upper-bound hypothesis is necessary: for a larger pre-sale size the expected payoff is zero while the displayed cube is negative.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 24 (PDF p. 25), paragraph after Proposition 3 and (16); p. 40 (PDF p. 41), (37)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.OptToken

theorem eq_16_lhs (c θ t : ℝ) (hc : 0 < c) (ht : 0 ≤ t)
    (hupper : c + 2 * t ≤ θ) :
    TokenFinance.Debt.expect θ (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) =
      c / (c + t) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3 := by sorry

end TokenFinance.OptToken
