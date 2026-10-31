-- Prove2me | Theorems.Thm_TokenSignal_Asymmetry_low_type_indifference
-- name    : TokenSignal.Asymmetry.low_type_indifference
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:58.173767+00:00
-- url     : https://prove2.me/theorems/a183dbc7-cd1a-48be-a450-178d0e6ed936
-- title:
--   Low-type indifference at the threshold
-- statement:
--   At the threshold $\alpha^*$, the low-quality entrepreneur is indifferent between selling that fraction and being perceived as high-quality, and selling the entire venture while being perceived correctly:
--
--   $$U_{LH}(\alpha^*)=U_{LL}(1).$$
--
--   This indifference identifies the greatest stake the low type is willing to retain while imitating the high type.
-- source:
--   Chod & Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (version of Dec. 14, 2019), p. 21 (PDF 22), paragraph following Proposition 5

import Mathlib
import Definitions.Def_TokenSignal_Asymmetry_Model

namespace TokenSignal.Asymmetry

theorem low_type_indifference (P : Params) (hS : P.Standing) :
    U P .L .H (αStar P) = U P .L .L 1 := by sorry
end TokenSignal.Asymmetry
