-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_mem_center_of_val_scalar
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.mem_center_of_val_scalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:43:54.109544+00:00
-- url     : https://prove2.me/theorems/38bd36a6-b694-44cb-9458-26b9af169cd1
-- title:
--   Quaternion Generators: mem center of val scalar
-- statement:
--   The Quaternion Generators construction uses the mem center of val scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionGenerators.lean#L116-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionGenerators.lean#L116-L125

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

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.mem_center_of_val_scalar {epsilon y : K} (a : (Model epsilon y)ˣ)
    (r : K) (hScalar : (a : Model epsilon y) = (r : Model epsilon y)) :
    a ∈ Subgroup.center (Model epsilon y)ˣ := by sorry
