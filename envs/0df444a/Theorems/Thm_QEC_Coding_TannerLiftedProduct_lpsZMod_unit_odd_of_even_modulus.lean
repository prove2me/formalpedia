-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_unit_odd_of_even_modulus
-- name    : QEC.Coding.TannerLiftedProduct.lpsZMod_unit_odd_of_even_modulus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:47:40.701209+00:00
-- url     : https://prove2.me/theorems/a1d71ac4-11a2-45f0-9cd9-6d56bb41f138
-- title:
--   Tanner Lifted Product: lps ZMod unit odd of even modulus
-- statement:
--   A unit at an even positive modulus has an odd integer coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L338-L347
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L338-L347

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsZMod_unit_odd_of_even_modulus (N : ℕ) [NeZero N] (hN : 2 ∣ N)
    (a : ℤ) (ha : IsUnit (a:ZMod N)) : Odd a := by sorry
