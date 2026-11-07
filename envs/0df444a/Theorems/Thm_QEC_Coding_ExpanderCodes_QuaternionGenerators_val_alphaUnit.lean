-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_alphaUnit
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:43:48.459708+00:00
-- url     : https://prove2.me/theorems/05279b5c-b164-472e-b4f8-3addbd032b81
-- title:
--   Quaternion Generators: val alpha Unit
-- statement:
--   The Quaternion Generators construction uses the val alpha Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionGenerators.lean#L93-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionGenerators.lean#L93-L94

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

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit (epsilon y : K) (hEpsilon : epsilon ≠ 0) :
    (alphaUnit epsilon y hEpsilon : Model epsilon y) = alpha epsilon y := by sorry

attribute [defeq] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
