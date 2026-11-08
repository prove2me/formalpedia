-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_sum_faceSquareGraph_eq_card_filter
-- name    : QEC.Coding.TannerLiftedProduct.sum_faceSquareGraph_eq_card_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:39:46.874331+00:00
-- url     : https://prove2.me/theorems/b8065eb7-c3fc-4565-ac89-88fe7fa3b151
-- title:
--   Tanner Lifted Product: sum face Square Graph eq card filter
-- statement:
--   Outgoing face-square multiplicity into a vertex set counts the local
--   direction pairs whose opposite face vertex lies in that set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L115-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L115-L124

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.sum_faceSquareGraph_eq_card_filter
    (label : W → G) (L : Finset (VertexIndex G)) (v : VertexIndex G) :
    ∑ u ∈ L, faceSquareGraph label v u =
      (Finset.univ.filter fun p : W × W =>
        verticalNeighbor label (horizontalNeighbor label v p.1) p.2 ∈ L).card := by sorry
