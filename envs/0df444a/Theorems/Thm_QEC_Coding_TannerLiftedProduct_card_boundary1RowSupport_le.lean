-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_boundary1RowSupport_le
-- name    : QEC.Coding.TannerLiftedProduct.card_boundary1RowSupport_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:13:11.17517+00:00
-- url     : https://prove2.me/theorems/0006540b-e0bf-4476-addd-e9cc8e0fc2c0
-- title:
--   Tanner Lifted Product: card boundary1 Row Support le
-- statement:
--   First-boundary checks have weight at most `w + 2r'`, independently of
--   the voltage-group size.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L283-L296
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L283-L296

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

theorem QEC.Coding.TannerLiftedProduct.card_boundary1RowSupport_le
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c0 : LiftedProduct.C0Index (Fin 2 × R) W G) :
    (LiftedProduct.boundary1RowSupport (data label h g') c0).card ≤
      Fintype.card W + 2 * Fintype.card R' := by sorry
