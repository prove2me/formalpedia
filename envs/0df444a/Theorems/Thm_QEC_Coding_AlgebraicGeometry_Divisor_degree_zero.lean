-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
-- name    : QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:10:08.312279+00:00
-- url     : https://prove2.me/theorems/27febab2-6ac4-43bd-876d-d3055428a32e
-- title:
--   Divisor: degree zero
-- statement:
--   The Divisor construction uses the degree zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/Divisor.lean#L46-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/Divisor.lean#L46-L47

import Mathlib.Data.Finsupp.Weight
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
open QEC.Coding.AlgebraicGeometry.Divisor
variable {P : Type*}

theorem QEC.Coding.AlgebraicGeometry.Divisor.degree_zero (degreeOf : P → ℕ) : degree degreeOf (0 : Divisor P) = 0 := by sorry
