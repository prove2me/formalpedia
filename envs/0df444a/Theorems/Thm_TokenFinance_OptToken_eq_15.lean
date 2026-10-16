-- Prove2me | Theorems.Thm_TokenFinance_OptToken_eq_15
-- name    : TokenFinance.OptToken.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:33.041934+00:00
-- url     : https://prove2.me/theorems/f6dc0d95-45ec-4e94-b004-5e7839555680
-- title:
--   Equation (15): no profitable overproduction in the low-demand case
-- statement:
--   Let $c,t>0$. If the unconstrained monopoly quantity $(x-c)/2$ does not exceed the pre-sale $t$, producing the nonnegative monopoly quantity pays the entrepreneur zero. Every output $q>t$ instead pays her strictly less than zero:
--
--   $$\pi_t^e(x,q^m(x))=0,\qquad q>t\Longrightarrow\pi_t^e(x,q)<0.$$
--
--   The refund and redemption rule therefore removes an incentive to issue extra tokens in the low-demand case. **Formalization Note** The weak inequality $(x-c)/2\le t$ includes the boundary, where the same strict loss holds for all $q>t$.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), pp. 23–24 (PDF pp. 24–25), Case 2 and (15)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.OptToken

theorem eq_15 (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    ∀ x : ℝ, (x - c) / 2 ≤ t →
      TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x) = 0 ∧
      ∀ q : ℝ, t < q → TokenFinance.Debt.tokEnt c t x q < 0 := by sorry

end TokenFinance.OptToken
