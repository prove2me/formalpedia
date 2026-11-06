-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_IsFullConstantField_mem_range
-- name    : QEC.Coding.AlgebraicGeometry.IsFullConstantField.mem_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T15:01:23.812004+00:00
-- url     : https://prove2.me/theorems/78865a44-68f7-40d8-b9c5-4ce9e7ece921
-- title:
--   Is Full Constant Field: mem range
-- statement:
--   An algebraic function-field element belongs to the range of the constant
--   embedding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/FullConstantField.lean#L41-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/FullConstantField.lean#L41-L44

import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_FullConstantField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped RatFunc
open QEC.Coding.AlgebraicGeometry.IsFullConstantField
variable (k F : Type*) [Field k] [Field F] [Algebra k F] [IsFullConstantField k F]

theorem QEC.Coding.AlgebraicGeometry.IsFullConstantField.mem_range {x : F} (hx : IsAlgebraic k x) :
    x ∈ Set.range (algebraMap k F) := by sorry
