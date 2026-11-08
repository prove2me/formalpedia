-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_horizontalNeighbor_horizontalNeighbor
-- name    : QEC.Coding.TannerLiftedProduct.horizontalNeighbor_horizontalNeighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:00:51.188561+00:00
-- url     : https://prove2.me/theorems/86a59e6b-70d2-49bc-9c40-377784293b1c
-- title:
--   Tanner Lifted Product: horizontal Neighbor horizontal Neighbor
-- statement:
--   A fixed horizontal direction is an involution on product vertices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L232-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L232-L237

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

theorem QEC.Coding.TannerLiftedProduct.horizontalNeighbor_horizontalNeighbor
    (label : W → G) (v : VertexIndex G) (a : W) :
    horizontalNeighbor label (horizontalNeighbor label v a) a = v := by sorry
