-- Prove2me | Theorems.Thm_TokenSignal_Asymmetry_low_ic_iff
-- name    : TokenSignal.Asymmetry.low_ic_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:01.263976+00:00
-- url     : https://prove2.me/theorems/74e340c4-f978-4857-9aaa-a980c0df5dce
-- title:
--   Condition (24): low-type incentive threshold
-- statement:
--   For either financing method, take a feasible belief threshold $t$ with $\bar\alpha_H^i\le t<1$. The low type’s incentive condition (24) holds exactly when
--
--   $$t\le\alpha^*.$$
--
--   Condition (24) compares the best low-type payoff when investors believe $L$ with the best payoff from mimicking $H$.
-- source:
--   Chod & Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (version of Dec. 14, 2019), p. 31 (PDF 32), proof of Proposition 5 following eq. (38)

import Mathlib
import Definitions.Def_TokenSignal_Asymmetry_Model

namespace TokenSignal.Asymmetry

theorem low_ic_iff (P : Params) (hS : P.Standing) (m : Method) (t : ℝ)
    (htH : αbar P m .H ≤ t) (ht1 : t < 1) :
    LowIC P m t ↔ t ≤ αStar P := by sorry
end TokenSignal.Asymmetry
