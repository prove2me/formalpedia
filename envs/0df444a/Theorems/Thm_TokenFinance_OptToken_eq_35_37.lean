-- Prove2me | Theorems.Thm_TokenFinance_OptToken_eq_35_37
-- name    : TokenFinance.OptToken.eq_35_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:25.940872+00:00
-- url     : https://prove2.me/theorems/b680e67b-7dbb-43ae-b71e-f7884dc2d9a4
-- title:
--   Equations (35)–(37): investor break-even as a difference of integrals
-- statement:
--   Let $c,t>0$ and $c+2t\le\theta$. Investors hold the initial $t$ tokens and receive their share of later tokens under the contract of Proposition 3. Let $I_t(x)$ be their realized payoff when the entrepreneur produces $q^m(x)$, and let $C_0$ be the set-up cost. The condition $E_\theta[I_t]=C_0+ct$ is equivalent to
--
--   $$C_0=\int_c^\theta\frac{(x-c)^2}{4\theta}\,dx-\int_{c+2t}^\theta\frac1\theta\frac{c}{c+t}\left(\frac{x-c}{2}-t\right)^2\,dx.$$
--
--   This is the integral form from which equation (16) follows. **Formalization Note** Investor payments are integrated from the realized, piecewise token payoff. The upper-bound hypothesis puts the three integration regions of (35) in their stated order.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 40 (PDF p. 41), (35)–(37)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.OptToken

theorem eq_35_37 (c C0 θ t : ℝ) (hc : 0 < c) (ht : 0 < t)
    (hupper : c + 2 * t ≤ θ) :
    (TokenFinance.Debt.expect θ (fun x => TokenFinance.Debt.tokInv c t x (TokenFinance.Debt.qm c x)) = C0 + c * t) ↔
      C0 = (∫ x in c..θ, (x - c) ^ 2 / (4 * θ)) -
        ∫ x in (c + 2 * t)..θ,
          1 / θ * (c / (c + t) * ((x - c) / 2 - t) ^ 2) := by sorry

end TokenFinance.OptToken
