-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_mul_ne_mul_of_separated_squares
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.mul_ne_mul_of_separated_squares
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:44:01.469806+00:00
-- url     : https://prove2.me/theorems/a10c036d-59a8-40c2-8e3e-5667e7933630
-- title:
--   Quaternion Generators: mul ne mul of separated squares
-- statement:
--   An involution cannot be conjugate to an element whose square is nontrivial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionGenerators.lean#L180-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionGenerators.lean#L180-L189

import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
variable {H : Type*} [Group H]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.mul_ne_mul_of_separated_squares (a b g : H) (ha : a ^ 2 ≠ 1)
    (hb : b ^ 2 = 1) : a * g ≠ g * b := by sorry
