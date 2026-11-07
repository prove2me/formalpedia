-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_eight_four
-- name    : QEC.Coding.TannerLiftedProduct.lpsChar_eight_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:47:37.705648+00:00
-- url     : https://prove2.me/theorems/8333a791-1515-49e4-824c-f1b62b19f9aa
-- title:
--   Tanner Lifted Product: lps Char eight four
-- statement:
--   The actual modulus-eight half-turn character is minus one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L154-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L154-L158

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsChar_eight_four : ZMod.stdAddChar (4:ZMod 8)= -1 := by sorry
