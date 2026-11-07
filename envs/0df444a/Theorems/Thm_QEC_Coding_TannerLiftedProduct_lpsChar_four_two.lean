-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_four_two
-- name    : QEC.Coding.TannerLiftedProduct.lpsChar_four_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:47:51.32978+00:00
-- url     : https://prove2.me/theorems/eef24215-05ed-4438-8ff1-9dfbe474a021
-- title:
--   Tanner Lifted Product: lps Char four two
-- statement:
--   The actual modulus-four half-turn character is minus one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L147-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L147-L151

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsChar_four_two : ZMod.stdAddChar (2:ZMod 4)= -1 := by sorry
