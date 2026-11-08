-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_horizontalFiberBoundaryMoveAtVertex_face_eq_zero_of_not_mem
-- name    : QEC.Coding.TannerLiftedProduct.horizontalFiberBoundaryMoveAtVertex_face_eq_zero_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:38:55.40293+00:00
-- url     : https://prove2.me/theorems/e55f0be4-1a60-468b-9681-f919dfe9a97d
-- title:
--   Tanner Lifted Product: horizontal Fiber Boundary Move At Vertex face eq zero of not mem
-- statement:
--   A horizontal fiber move vanishes on every face outside its one incident
--   column.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1359-L1384
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1359-L1384

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

theorem QEC.Coding.TannerLiftedProduct.horizontalFiberBoundaryMoveAtVertex_face_eq_zero_of_not_mem
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (v : VertexIndex G) (a : W) (u : Word F R') (p : FaceIndex W G)
    (hp : p ∉ horizontalFaceColumn label v a) :
    horizontalFiberBoundaryMoveAtVertex label h g' v a u
        (faceCoordinate (R := R) (R' := R') p) = 0 := by sorry
