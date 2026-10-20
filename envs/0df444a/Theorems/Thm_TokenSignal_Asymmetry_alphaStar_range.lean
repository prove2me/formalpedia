-- Prove2me | Theorems.Thm_TokenSignal_Asymmetry_alphaStar_range
-- name    : TokenSignal.Asymmetry.alphaStar_range
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:54.883433+00:00
-- url     : https://prove2.me/theorems/11bab711-ff2c-4767-a1a2-43a962a7f844
-- title:
--   Equation (25): interior signaling threshold
-- statement:
--   With $\mu_H>\mu_L$, $\gamma>0$ and $\sigma>0$, define the signaling threshold $\alpha^*$ by equation (25). It lies strictly inside the unit interval:
--
--   $$0<\alpha^*<1.$$
--
--   This ensures that the threshold can describe a genuine retained stake.
-- source:
--   Chod & Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (version of Dec. 14, 2019), p. 20 (PDF 21), eq. (25)

import Mathlib
import Definitions.Def_TokenSignal_Asymmetry_Model

namespace TokenSignal.Asymmetry

theorem alphaStar_range (P : Params) (hS : P.Standing) :
    0 < αStar P ∧ αStar P < 1 := by sorry
end TokenSignal.Asymmetry
