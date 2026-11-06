-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_isFullConstantField_iff_algebraicClosure_eq_bot
-- name    : QEC.Coding.AlgebraicGeometry.isFullConstantField_iff_algebraicClosure_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:29:03.435187+00:00
-- url     : https://prove2.me/theorems/a13e83c1-0313-460c-956a-c4683c070943
-- title:
--   Algebraic Geometry: is Full Constant Field iff algebraic Closure eq bot
-- statement:
--   Full constants are equivalent to the relative algebraic closure of `k`
--   inside `F` being the bottom intermediate field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/FullConstantField.lean#L50-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/FullConstantField.lean#L50-L64

import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_FullConstantField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped RatFunc

theorem QEC.Coding.AlgebraicGeometry.isFullConstantField_iff_algebraicClosure_eq_bot
    (k F : Type*) [Field k] [Field F] [Algebra k F] :
    IsFullConstantField k F ↔ algebraicClosure k F = ⊥ := by sorry
