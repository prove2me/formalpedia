-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_boundary2RowSupport_le
-- name    : QEC.Coding.TannerLiftedProduct.card_boundary2RowSupport_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:12:44.645756+00:00
-- url     : https://prove2.me/theorems/9aff4cd5-a865-4fd0-95ff-bfa59139ed8e
-- title:
--   Tanner Lifted Product: card boundary2 Row Support le
-- statement:
--   Second-boundary checks have weight at most `w + 2r`, independently of
--   the voltage-group size.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L366-L379
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L366-L379

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldCSSPresentation
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.LiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.card_boundary2RowSupport_le
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c2 : LiftedProduct.C2Index W (Fin 2 × R') G) :
    (LiftedProduct.boundary2RowSupport (data label h g') c2).card ≤
      Fintype.card W + 2 * Fintype.card R := by sorry
