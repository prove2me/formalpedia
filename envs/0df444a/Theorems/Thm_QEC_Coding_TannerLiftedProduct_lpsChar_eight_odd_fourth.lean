-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_eight_odd_fourth
-- name    : QEC.Coding.TannerLiftedProduct.lpsChar_eight_odd_fourth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:48:13.367192+00:00
-- url     : https://prove2.me/theorems/2a97880c-23de-4016-ae0e-ce0262066f97
-- title:
--   Tanner Lifted Product: lps Char eight odd fourth
-- statement:
--   An odd input gives the modulus-eight character fourth power minus one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L173-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L173-L185

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsChar_eight_odd_fourth (a : ℤ) (ha : Odd a) :
    ZMod.stdAddChar (a:ZMod 8)^4= -1 := by sorry
