-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_add
-- name    : QEC.Coding.AlgebraicGeometry.Divisor.degree_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:13:15.17957+00:00
-- url     : https://prove2.me/theorems/340c5151-57bf-4be5-95a4-3130a5a701de
-- title:
--   Divisor: degree add
-- statement:
--   The Divisor construction uses the degree add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/Divisor.lean#L49-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/Divisor.lean#L49-L51

import Mathlib.Data.Finsupp.Weight
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
open QEC.Coding.AlgebraicGeometry.Divisor
variable {P : Type*}

theorem QEC.Coding.AlgebraicGeometry.Divisor.degree_add (degreeOf : P → ℕ) (D E : Divisor P) :
    degree degreeOf (D + E) = degree degreeOf D + degree degreeOf E := by sorry
