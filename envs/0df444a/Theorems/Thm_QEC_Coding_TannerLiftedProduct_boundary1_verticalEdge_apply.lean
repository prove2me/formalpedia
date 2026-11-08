-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_boundary1_verticalEdge_apply
-- name    : QEC.Coding.TannerLiftedProduct.boundary1_verticalEdge_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:37:31.293926+00:00
-- url     : https://prove2.me/theorems/b0c371ab-f248-493b-9a68-6870a5bcb49c
-- title:
--   Tanner Lifted Product: boundary1 vertical Edge apply
-- statement:
--   The full vertical-edge boundary equation is the local face syndrome plus
--   the two endpoint vertex contributions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L361-L386
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L361-L386

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.boundary1_verticalEdge_apply
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (r : R) (b : W) :
    LiftedProduct.boundary1 (data label h h') c
        (verticalEdgeCoordinate label v r b) =
      (∑ a, h r a *
        c (faceCoordinate (R := R) (R' := R')
          (faceAtVertex label v a b))) +
      ∑ endpoint : Fin 2 × R',
        (-h' endpoint.2 b) *
          c (verticalEndpointCoordinate label v r b endpoint.1 endpoint.2) := by sorry
