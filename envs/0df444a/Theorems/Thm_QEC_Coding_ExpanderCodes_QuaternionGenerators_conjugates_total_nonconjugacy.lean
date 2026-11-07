-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_conjugates_total_nonconjugacy
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.conjugates_total_nonconjugacy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:46:23.009091+00:00
-- url     : https://prove2.me/theorems/4d0f021f-6b51-4b84-a7ba-1b6db22d633d
-- title:
--   Quaternion Generators: conjugates total nonconjugacy
-- statement:
--   The actual quaternion generators, and all their conjugates, satisfy the
--   total-nonconjugacy equation used by the left/right square construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionGenerators.lean#L204-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionGenerators.lean#L204-L213

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

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.conjugates_total_nonconjugacy (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (s t g : ProjectiveGroup epsilon y) :
    (s * projectiveBase epsilon y hY hOne * s⁻¹) * g ≠
      g * (t * projectivePrime epsilon y hEpsilon hY hOne * t⁻¹) := by sorry
