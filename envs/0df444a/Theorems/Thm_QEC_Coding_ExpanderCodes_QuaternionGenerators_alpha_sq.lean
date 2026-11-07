-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_alpha_sq
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.alpha_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:29:41.438066+00:00
-- url     : https://prove2.me/theorems/77aa5aa2-6278-446e-89fb-f44544bb6ff8
-- title:
--   Quaternion Generators: alpha sq
-- statement:
--   The Quaternion Generators construction uses the alpha sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionGenerators.lean#L43-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionGenerators.lean#L43-L44

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

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.alpha_sq (epsilon y : K) : alpha epsilon y ^ 2 = (epsilon : Model epsilon y) := by sorry
