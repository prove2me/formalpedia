-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_unit_descend
-- name    : QEC.Coding.TannerLiftedProduct.lpsZMod_unit_descend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:47:31.276603+00:00
-- url     : https://prove2.me/theorems/d393a910-9ced-448b-8972-1268f25449a5
-- title:
--   Tanner Lifted Product: lps ZMod unit descend
-- statement:
--   A genuine unit maps to a unit at a dividing positive modulus.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L317-L320
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L317-L320

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsZMod_unit_descend (N m : ℕ) [NeZero N] [NeZero m]
    (hm : m ∣ N) (a : ℤ) (ha : IsUnit (a:ZMod N)) : IsUnit (a:ZMod m) := by sorry
