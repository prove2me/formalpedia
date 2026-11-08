-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_boundary1_verticalEdge_matrix_apply
-- name    : QEC.Coding.TannerLiftedProduct.boundary1_verticalEdge_matrix_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:37:47.523542+00:00
-- url     : https://prove2.me/theorems/759757bf-963e-4e9d-9acc-70d69ff11317
-- title:
--   Tanner Lifted Product: boundary1 vertical Edge matrix apply
-- statement:
--   Matrix form of the vertical-edge boundary equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L577-L589
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L577-L589

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

theorem QEC.Coding.TannerLiftedProduct.boundary1_verticalEdge_matrix_apply
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (r : R) (b : W) :
    LiftedProduct.boundary1 (data label h h') c
        (verticalEdgeCoordinate label v r b) =
      (localFaceMatrix label c v * h.transpose) b r -
        verticalEndpointSyndrome label h' c v b r := by sorry
