-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardTheta_slash_neg_matrix
-- name    : QEC.Coding.TannerLiftedProduct.lpsStandardTheta_slash_neg_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:48:41.53364+00:00
-- url     : https://prove2.me/theorems/7f00786c-783e-4031-8742-173c48e9aee6
-- title:
--   Tanner Lifted Product: lps Standard Theta slash neg matrix
-- statement:
--   Weight two removes the matrix-negation sign without changing its action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCusps.lean#L194-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCusps.lean#L194-L204

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsStandardTheta_slash_neg_matrix (q : ℕ) (γ : SL(2,ℤ)) :
    ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] (-γ)) =
      ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ) := by sorry
