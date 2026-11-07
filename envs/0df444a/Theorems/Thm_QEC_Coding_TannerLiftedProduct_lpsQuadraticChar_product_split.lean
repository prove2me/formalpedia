-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticChar_product_split
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticChar_product_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:47:59.243988+00:00
-- url     : https://prove2.me/theorems/2921b4d8-3072-4e3d-a0d8-5f4724a12351
-- title:
--   Tanner Lifted Product: lps Quadratic Char product split
-- statement:
--   The CRT quadratic cross term has zero character phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L107-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L107-L117

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticChar_product_split (m n : ℕ) [NeZero m] [NeZero n]
    (a x y : ℤ) :
    ZMod.stdAddChar (((a*((n:ℤ)*x+(m:ℤ)*y)^2):ℤ):ZMod (m*n)) =
      ZMod.stdAddChar (((a*(n:ℤ)*x^2):ℤ):ZMod m)*
      ZMod.stdAddChar (((a*(m:ℤ)*y^2):ℤ):ZMod n) := by sorry
