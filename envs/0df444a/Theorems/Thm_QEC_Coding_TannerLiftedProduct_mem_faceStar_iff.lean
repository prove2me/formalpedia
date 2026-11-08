-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_faceStar_iff
-- name    : QEC.Coding.TannerLiftedProduct.mem_faceStar_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:37:07.395981+00:00
-- url     : https://prove2.me/theorems/5c40ab68-df73-4c8e-a2e2-fc094272fd9d
-- title:
--   Tanner Lifted Product: mem face Star iff
-- statement:
--   Membership in a vertex face star has explicit local coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L76-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L76-L85

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

theorem QEC.Coding.TannerLiftedProduct.mem_faceStar_iff (label : W → G) (v : VertexIndex G)
    (p : FaceIndex W G) :
    p ∈ faceStar label v ↔ ∃ a b, faceAtVertex label v a b = p := by sorry
