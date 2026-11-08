-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_vertexAtFaceSides_eq_of_mem_faceStar
-- name    : QEC.Coding.TannerLiftedProduct.vertexAtFaceSides_eq_of_mem_faceStar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:01:58.022802+00:00
-- url     : https://prove2.me/theorems/63267703-59ba-4d52-affe-64bb01988322
-- title:
--   Tanner Lifted Product: vertex At Face Sides eq of mem face Star
-- statement:
--   Face incidence determines the vertex once its two side bits are known.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L155-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L155-L161

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
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.vertexAtFaceSides_eq_of_mem_faceStar
    (label : W → G) (v : VertexIndex G) (p : FaceIndex W G)
    (hp : p ∈ faceStar label v) :
    vertexAtFaceSides label p v.1 v.2.1 = v := by sorry
