-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_activeVerticalEdges_le_card_mul_blockWeight
-- name    : QEC.Coding.TannerLiftedProduct.card_activeVerticalEdges_le_card_mul_blockWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:02:47.905764+00:00
-- url     : https://prove2.me/theorems/1f117a71-05db-4a13-bcda-d555fb63937d
-- title:
--   Tanner Lifted Product: card active Vertical Edges le card mul block Weight
-- statement:
--   For local degree at least two, the number of active vertical edges is at
--   most `w` times the PK22 block weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L327-L345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L327-L345

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
omit [Fintype F] [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.card_activeVerticalEdges_le_card_mul_blockWeight
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hTwo : 2 ≤ Fintype.card W) :
    (activeVerticalEdges label c).card ≤ Fintype.card W * blockWeight c := by sorry
