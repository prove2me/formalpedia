-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_neg
-- name    : QEC.Coding.AlgebraicGeometry.Divisor.degree_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:49:33.463357+00:00
-- url     : https://prove2.me/theorems/8b26de8a-7bd8-4ae3-9f34-b5da65bdc232
-- title:
--   Divisor: degree neg
-- statement:
--   The Divisor construction uses the degree neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/Divisor.lean#L53-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/Divisor.lean#L53-L55

import Mathlib.Data.Finsupp.Weight
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
open QEC.Coding.AlgebraicGeometry.Divisor
variable {P : Type*}

theorem QEC.Coding.AlgebraicGeometry.Divisor.degree_neg (degreeOf : P → ℕ) (D : Divisor P) :
    degree degreeOf (-D) = -degree degreeOf D := by sorry
