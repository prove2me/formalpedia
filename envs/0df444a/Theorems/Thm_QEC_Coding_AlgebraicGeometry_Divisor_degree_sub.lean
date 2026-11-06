-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_sub
-- name    : QEC.Coding.AlgebraicGeometry.Divisor.degree_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:13:09.667548+00:00
-- url     : https://prove2.me/theorems/26c6cadd-f08d-492b-b45c-1c3e74c378c0
-- title:
--   Divisor: degree sub
-- statement:
--   The Divisor construction uses the degree sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/Divisor.lean#L57-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/Divisor.lean#L57-L59

import Mathlib.Data.Finsupp.Weight
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
open QEC.Coding.AlgebraicGeometry.Divisor
variable {P : Type*}

theorem QEC.Coding.AlgebraicGeometry.Divisor.degree_sub (degreeOf : P → ℕ) (D E : Divisor P) :
    degree degreeOf (D - E) = degree degreeOf D - degree degreeOf E := by sorry
