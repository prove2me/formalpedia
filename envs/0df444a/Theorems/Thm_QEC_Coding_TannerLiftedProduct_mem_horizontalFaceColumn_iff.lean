-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_horizontalFaceColumn_iff
-- name    : QEC.Coding.TannerLiftedProduct.mem_horizontalFaceColumn_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:34:05.187679+00:00
-- url     : https://prove2.me/theorems/d0a34410-b1c3-4425-8e33-7de9016bcae0
-- title:
--   Tanner Lifted Product: mem horizontal Face Column iff
-- statement:
--   The Tanner Lifted Product construction uses the mem horizontal Face Column iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1171-L1181
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1171-L1181

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
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.mem_horizontalFaceColumn_iff
    (label : W → G) (v : VertexIndex G) (a : W) (p : FaceIndex W G) :
    p ∈ horizontalFaceColumn label v a ↔
      ∃ b, faceAtVertex label v a b = p := by sorry
