-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalBaseInfinityCancellation_rationalInfinity_order_add_normalizedDegree
-- name    : QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation.rationalInfinity_order_add_normalizedDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:44:43.743793+00:00
-- url     : https://prove2.me/theorems/6bc975d7-4a56-494b-8fba-1033182ea3a4
-- title:
--   Rational Base Infinity Cancellation: rational Infinity order add normalized Degree
-- statement:
--   The infinity contribution cancels the numerator-minus-denominator degree
--   term exactly.  This is the terminal cancellation used by the finite-place
--   factorization construction in the next dependency step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/RationalBaseInfinityCancellation.lean#L31-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/RationalBaseInfinityCancellation.lean#L31-L36

import Mathlib.FieldTheory.RatFunc.Degree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation
open scoped RatFunc WithZero
variable (k : Type*) [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation.rationalInfinity_order_add_normalizedDegree
    (f : RatFunc k) (hf : f ≠ 0) :
    GlobalPlace.order (GlobalPlace.rationalInfinity k) f +
        ((f.num.natDegree : ℤ) - f.denom.natDegree) = 0 := by sorry
