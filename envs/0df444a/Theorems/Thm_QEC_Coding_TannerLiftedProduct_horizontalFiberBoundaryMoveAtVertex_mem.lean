-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_horizontalFiberBoundaryMoveAtVertex_mem
-- name    : QEC.Coding.TannerLiftedProduct.horizontalFiberBoundaryMoveAtVertex_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:39:30.367433+00:00
-- url     : https://prove2.me/theorems/5c77acf3-5891-4102-8505-e28a9f3dd96a
-- title:
--   Tanner Lifted Product: horizontal Fiber Boundary Move At Vertex mem
-- statement:
--   Every explicit fiber move occurs in the finite source-local move set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1422-L1429
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1422-L1429

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

theorem QEC.Coding.TannerLiftedProduct.horizontalFiberBoundaryMoveAtVertex_mem
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (v : VertexIndex G) (a : W) (u : Word F R') :
    horizontalFiberBoundaryMoveAtVertex label h g' v a u ∈
      horizontalFiberBoundaryMoves label h g' := by sorry
