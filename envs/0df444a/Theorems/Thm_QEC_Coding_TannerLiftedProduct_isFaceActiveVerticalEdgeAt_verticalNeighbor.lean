-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_isFaceActiveVerticalEdgeAt_verticalNeighbor
-- name    : QEC.Coding.TannerLiftedProduct.isFaceActiveVerticalEdgeAt_verticalNeighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:03:07.778367+00:00
-- url     : https://prove2.me/theorems/009bcc32-073f-4669-befa-1685ddecab9c
-- title:
--   Tanner Lifted Product: is Face Active Vertical Edge At vertical Neighbor
-- statement:
--   Face-activity is independent of which endpoint represents a physical
--   vertical edge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L621-L631
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L621-L631

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [DecidableEq G] [Fintype W] [DecidableEq W]
    [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.isFaceActiveVerticalEdgeAt_verticalNeighbor
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (b : W)
    (he : IsFaceActiveVerticalEdgeAt label c v b) :
    IsFaceActiveVerticalEdgeAt label c (verticalNeighbor label v b) b := by sorry
