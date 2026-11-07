-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_eq_scalar_of_mem_center
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.val_eq_scalar_of_mem_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:33:20.869711+00:00
-- url     : https://prove2.me/theorems/4aa499ca-ca96-4052-bacb-bf12e3433a33
-- title:
--   Quaternion Generators: val eq scalar of mem center
-- statement:
--   Central quaternion units have no non-scalar coordinates in odd characteristic.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L37-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L37-L57

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.val_eq_scalar_of_mem_center (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (a : (Model epsilon y)ˣ) (ha : a ∈ Subgroup.center (Model epsilon y)ˣ) :
    (a : Model epsilon y) = (((a : Model epsilon y).re : K) : Model epsilon y) := by sorry
