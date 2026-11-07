-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_conjugate_sq_ne_one
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.conjugate_sq_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:44:11.117545+00:00
-- url     : https://prove2.me/theorems/a164fb90-9205-4b0a-938c-a2b19511ed1d
-- title:
--   Quaternion Generators: conjugate sq ne one
-- statement:
--   Nontriviality of a square is preserved by conjugation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionGenerators.lean#L192-L198
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionGenerators.lean#L192-L198

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

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.conjugate_sq_ne_one (a t : H) (ha : a ^ 2 ≠ 1) :
    (t * a * t⁻¹) ^ 2 ≠ 1 := by sorry
