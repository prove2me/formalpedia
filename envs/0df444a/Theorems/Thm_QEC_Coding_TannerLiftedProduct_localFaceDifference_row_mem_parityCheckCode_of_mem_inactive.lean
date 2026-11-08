-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_localFaceDifference_row_mem_parityCheckCode_of_mem_inactive
-- name    : QEC.Coding.TannerLiftedProduct.localFaceDifference_row_mem_parityCheckCode_of_mem_inactive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:38:40.356298+00:00
-- url     : https://prove2.me/theorems/7b9a6cfc-960a-4b11-96ee-69b600f5e5bc
-- title:
--   Tanner Lifted Product: local Face Difference row mem parity Check Code of mem inactive
-- statement:
--   On every inactive direction, the face/coset-leader difference is a word
--   of the first local code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L697-L719
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L697-L719

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

theorem QEC.Coding.TannerLiftedProduct.localFaceDifference_row_mem_parityCheckCode_of_mem_inactive
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hc : LiftedProduct.boundary1 (data label h h') c = 0)
    (v : VertexIndex G) (b : W)
    (hb : b ∈ verticalInactiveDirections label c v) :
    ProductExpansion.row (localFaceDifference label h hRank h' c v) b ∈
      (ProductExpansion.parityCheckCode h).carrier := by sorry
