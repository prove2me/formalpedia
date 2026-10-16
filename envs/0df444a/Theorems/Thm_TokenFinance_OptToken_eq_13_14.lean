-- Prove2me | Theorems.Thm_TokenFinance_OptToken_eq_13_14
-- name    : TokenFinance.OptToken.eq_13_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:28.430214+00:00
-- url     : https://prove2.me/theorems/baca39bc-e5a8-4897-a645-e7da557495a8
-- title:
--   Equations (13)–(14): entrepreneur's high-output payoff
-- statement:
--   Let $c,t>0$. If output $q$ exceeds the pre-sale $t$, the entrepreneur's realized token-contract payoff is
--
--   $$\pi_t^e(x,q)=\frac{c}{c+t}(q-t)(x-q-c-t).$$
--
--   If $q^m(x)=(x-c)/2>t$, then
--
--   $$\pi_t^e(x,q^m(x))=\frac{c}{c+t}\left(\frac{x-c}{2}-t\right)^2>0.$$
--
--   These formulas identify the positive-payoff branch of the optimal token contract.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 23 (PDF p. 24), (13)–(14)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.OptToken

theorem eq_13_14 (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    (∀ x q : ℝ, t < q →
      TokenFinance.Debt.tokEnt c t x q = c / (c + t) * (q - t) * (x - q - c - t)) ∧
    (∀ x : ℝ, t < (x - c) / 2 →
      TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x) = c / (c + t) * ((x - c) / 2 - t) ^ 2 ∧
      0 < TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) := by sorry

end TokenFinance.OptToken
