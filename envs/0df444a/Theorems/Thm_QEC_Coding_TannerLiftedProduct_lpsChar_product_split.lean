-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_product_split
-- name    : QEC.Coding.TannerLiftedProduct.lpsChar_product_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:47:50.185693+00:00
-- url     : https://prove2.me/theorems/a0d76664-af85-4b87-8960-a5eea03a3afd
-- title:
--   Tanner Lifted Product: lps Char product split
-- statement:
--   Actual character inflation splits the two CRT linear contributions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L99-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L99-L104

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsChar_product_split (m n : ℕ) [NeZero m] [NeZero n] (x y : ℤ) :
    ZMod.stdAddChar (((n:ℤ)*x+(m:ℤ)*y:ℤ):ZMod (m*n)) =
      ZMod.stdAddChar (x:ZMod m)*ZMod.stdAddChar (y:ZMod n) := by sorry
