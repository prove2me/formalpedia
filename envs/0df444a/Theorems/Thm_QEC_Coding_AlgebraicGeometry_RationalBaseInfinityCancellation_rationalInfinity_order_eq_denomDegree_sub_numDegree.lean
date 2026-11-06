-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalBaseInfinityCancellation_rationalInfinity_order_eq_denomDegree_sub_numDegree
-- name    : QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation.rationalInfinity_order_eq_denomDegree_sub_numDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:48:36.133201+00:00
-- url     : https://prove2.me/theorems/53e4d7f1-9610-47ac-a749-db9b7165c9a1
-- title:
--   Rational Base Infinity Cancellation: rational Infinity order eq denom Degree sub num Degree
-- statement:
--   The same actual order, expanded through the normalized numerator and
--   denominator chosen by `RatFunc`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/RationalBaseInfinityCancellation.lean#L21-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/RationalBaseInfinityCancellation.lean#L21-L26

import Mathlib.FieldTheory.RatFunc.Degree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation
open scoped RatFunc WithZero
variable (k : Type*) [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation.rationalInfinity_order_eq_denomDegree_sub_numDegree
    (f : RatFunc k) (hf : f ≠ 0) :
    GlobalPlace.order (GlobalPlace.rationalInfinity k) f =
      (f.denom.natDegree : ℤ) - f.num.natDegree := by sorry
