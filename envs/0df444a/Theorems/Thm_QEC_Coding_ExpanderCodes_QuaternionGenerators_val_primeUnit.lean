-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_primeUnit
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:43:47.790475+00:00
-- url     : https://prove2.me/theorems/66d4aea5-1c1d-4687-bc76-7c3092eee11f
-- title:
--   Quaternion Generators: val prime Unit
-- statement:
--   The Quaternion Generators construction uses the val prime Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionGenerators.lean#L99-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionGenerators.lean#L99-L102

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

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    (primeUnit epsilon y hEpsilon hY hOne : Model epsilon y) = prime epsilon y := by sorry
