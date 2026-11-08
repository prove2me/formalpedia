-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_faceSupport_inter_horizontalFaceColumn
-- name    : QEC.Coding.TannerLiftedProduct.card_faceSupport_inter_horizontalFaceColumn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:38:48.286749+00:00
-- url     : https://prove2.me/theorems/70ac8f4a-0885-4869-941a-05887863f5ff
-- title:
--   Tanner Lifted Product: card face Support inter horizontal Face Column
-- statement:
--   Active global faces in one horizontal star column are counted by the
--   Hamming weight of the corresponding local matrix column.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1197-L1244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1197-L1244

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
omit [Fintype F]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.card_faceSupport_inter_horizontalFaceColumn
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (a : W) :
    (faceSupport c ∩ horizontalFaceColumn label v a).card =
      HammingWeight
        (ProductExpansion.column (localFaceMatrix label c v) a) := by sorry
