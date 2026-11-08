-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_horizontalFiberBoundaryMoveAtVertex_neighbor_apply
-- name    : QEC.Coding.TannerLiftedProduct.horizontalFiberBoundaryMoveAtVertex_neighbor_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:48:05.597387+00:00
-- url     : https://prove2.me/theorems/11ff09a7-54d9-4817-b1f7-db187e5cd399
-- title:
--   Tanner Lifted Product: horizontal Fiber Boundary Move At Vertex neighbor apply
-- statement:
--   The other endpoint receives the same local outer-product update.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1339-L1354
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1339-L1354

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

theorem QEC.Coding.TannerLiftedProduct.horizontalFiberBoundaryMoveAtVertex_neighbor_apply
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (v : VertexIndex G) (a : W) (u : Word F R') (r : R) (r' : R') :
    horizontalFiberBoundaryMoveAtVertex label h g' v a u
        (vertexCoordinate (W := W) (horizontalNeighbor label v a) r r') =
      h r a * u r' := by sorry
