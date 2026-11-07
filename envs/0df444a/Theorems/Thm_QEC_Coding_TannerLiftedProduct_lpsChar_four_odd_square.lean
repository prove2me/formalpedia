-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_four_odd_square
-- name    : QEC.Coding.TannerLiftedProduct.lpsChar_four_odd_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:48:10.943274+00:00
-- url     : https://prove2.me/theorems/cb58f55b-d864-41b7-9f17-f446e7832a58
-- title:
--   Tanner Lifted Product: lps Char four odd square
-- statement:
--   An odd input gives the modulus-four character square minus one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L161-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L161-L170

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsChar_four_odd_square (a : ℤ) (ha : Odd a) :
    ZMod.stdAddChar (a:ZMod 4)^2= -1 := by sorry
