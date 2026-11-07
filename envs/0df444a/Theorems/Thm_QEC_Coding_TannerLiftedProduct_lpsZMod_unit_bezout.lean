-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_unit_bezout
-- name    : QEC.Coding.TannerLiftedProduct.lpsZMod_unit_bezout
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:48:32.737757+00:00
-- url     : https://prove2.me/theorems/f2e02165-dcbc-4135-846b-3f8cc8e4a44d
-- title:
--   Tanner Lifted Product: lps ZMod unit bezout
-- statement:
--   An actual modular unit yields an integer determinant-one equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L323-L335
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L323-L335

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsZMod_unit_bezout (N : ℕ) [NeZero N] (a : ℤ) (ha : IsUnit (a:ZMod N)) :
    ∃ b u : ℤ, a*u-b*(N:ℤ)=1 := by sorry
