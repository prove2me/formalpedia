-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
-- name    : QEC.Coding.TannerLiftedProduct.rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:00:41.632569+00:00
-- url     : https://prove2.me/theorems/89df44bf-042f-4850-946b-e4cf227af092
-- title:
--   Tanner Lifted Product: right Double Cover Neighbor right Double Cover Neighbor
-- statement:
--   A fixed generator direction is an involution on the right double cover.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L221-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L221-L228

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W]

theorem QEC.Coding.TannerLiftedProduct.rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
    (label : W → G) (x : Fin 2 × G) (a : W) :
    rightDoubleCoverNeighbor label
      (rightDoubleCoverNeighbor label x a) a = x := by sorry
