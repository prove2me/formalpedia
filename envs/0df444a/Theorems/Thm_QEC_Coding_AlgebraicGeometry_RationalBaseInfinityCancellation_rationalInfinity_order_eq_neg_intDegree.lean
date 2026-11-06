-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalBaseInfinityCancellation_rationalInfinity_order_eq_neg_intDegree
-- name    : QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation.rationalInfinity_order_eq_neg_intDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:45:54.816644+00:00
-- url     : https://prove2.me/theorems/c74d76b8-8a3a-4207-80e1-30ec5caee4a7
-- title:
--   Rational Base Infinity Cancellation: rational Infinity order eq neg int Degree
-- statement:
--   The actual infinity-place order is the negative normalized rational
--   function degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/RationalBaseInfinityCancellation.lean#L12-L17
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/RationalBaseInfinityCancellation.lean#L12-L17

import Mathlib.FieldTheory.RatFunc.Degree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation
open scoped RatFunc WithZero
variable (k : Type*) [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation.rationalInfinity_order_eq_neg_intDegree (f : RatFunc k) (hf : f ≠ 0) :
    GlobalPlace.order (GlobalPlace.rationalInfinity k) f = -f.intDegree := by sorry
