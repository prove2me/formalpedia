-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_nonnegative
-- name    : QEC.Coding.AlgebraicGeometry.Divisor.degree_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:43:47.83841+00:00
-- url     : https://prove2.me/theorems/b70c76e9-abda-4525-b246-c67bf0ed411f
-- title:
--   Divisor: degree nonnegative
-- statement:
--   A positive divisor has nonnegative degree when place degrees are natural numbers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/Divisor.lean#L77-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/Divisor.lean#L77-L80

import Mathlib.Data.Finsupp.Weight
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
open QEC.Coding.AlgebraicGeometry.Divisor
variable {P : Type*}

theorem QEC.Coding.AlgebraicGeometry.Divisor.degree_nonnegative (degreeOf : P → ℕ) (D : Divisor P) (hD : Nonnegative D) :
    0 ≤ degree degreeOf D := by sorry
