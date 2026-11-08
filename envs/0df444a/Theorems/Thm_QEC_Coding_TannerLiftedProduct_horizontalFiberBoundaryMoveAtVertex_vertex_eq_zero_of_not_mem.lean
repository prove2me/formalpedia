-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_horizontalFiberBoundaryMoveAtVertex_vertex_eq_zero_of_not_mem
-- name    : QEC.Coding.TannerLiftedProduct.horizontalFiberBoundaryMoveAtVertex_vertex_eq_zero_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:39:09.57436+00:00
-- url     : https://prove2.me/theorems/2a5a39f4-cdb6-46cd-a979-2c6cfa92939c
-- title:
--   Tanner Lifted Product: horizontal Fiber Boundary Move At Vertex vertex eq zero of not mem
-- statement:
--   A horizontal fiber move vanishes on every vertex block except the two
--   endpoints of its edge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1389-L1419
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1389-L1419

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
omit [DecidableEq F]

theorem QEC.Coding.TannerLiftedProduct.horizontalFiberBoundaryMoveAtVertex_vertex_eq_zero_of_not_mem
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (v x : VertexIndex G) (a : W) (u : Word F R') (r : R) (r' : R')
    (hx : x ∉ horizontalVertexEndpoints label v a) :
    horizontalFiberBoundaryMoveAtVertex label h g' v a u
        (vertexCoordinate (W := W) x r r') = 0 := by sorry
