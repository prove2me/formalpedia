-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_variableSupport_le
-- name    : QEC.Coding.TannerLiftedProduct.card_variableSupport_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:12:41.192146+00:00
-- url     : https://prove2.me/theorems/214de87a-6c19-43fa-a22a-de25c9612c06
-- title:
--   Tanner Lifted Product: card variable Support le
-- statement:
--   Each qubit is incident to at most `2(w+r+r')` checks, independently of
--   the voltage-group size.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L516-L544
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L516-L544

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

theorem QEC.Coding.TannerLiftedProduct.card_variableSupport_le
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (q : LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) :
    ((LiftedProduct.boundaryIncidence (data label h g')).variableSupport q).card ≤
      2 * (Fintype.card W + Fintype.card R + Fintype.card R') := by sorry
