-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_mem_support_iff
-- name    : QEC.Coding.AlgebraicGeometry.Divisor.mem_support_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:43:02.88538+00:00
-- url     : https://prove2.me/theorems/d80dbc0c-6673-4591-b7c3-b2772f982a52
-- title:
--   Divisor: mem support iff
-- statement:
--   A divisor has a place in its support exactly when its coefficient is nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/Divisor.lean#L25-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/Divisor.lean#L25-L28

import Mathlib.Data.Finsupp.Weight
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
open QEC.Coding.AlgebraicGeometry.Divisor
variable {P : Type*}

theorem QEC.Coding.AlgebraicGeometry.Divisor.mem_support_iff {D : Divisor P} {place : P} :
    place ∈ support D ↔ D place ≠ 0 := by sorry
