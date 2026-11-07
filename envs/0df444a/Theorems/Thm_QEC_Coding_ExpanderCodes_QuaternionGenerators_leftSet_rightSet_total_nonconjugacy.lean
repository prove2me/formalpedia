-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_leftSet_rightSet_total_nonconjugacy
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.leftSet_rightSet_total_nonconjugacy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:30:53.616195+00:00
-- url     : https://prove2.me/theorems/edb4b82b-21e9-4a94-8c47-bc8b8495df78
-- title:
--   Quaternion Generators: left Set right Set total nonconjugacy
-- statement:
--   The Quaternion Generators construction uses the left Set right Set total nonconjugacy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionCayleySets.lean#L123-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionCayleySets.lean#L123-L131

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionCayleySets
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.leftSet_rightSet_total_nonconjugacy (epsilon y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) {a b : ProjectiveGroup epsilon y}
    (ha : a ∈ leftSet epsilon y hEpsilon hY hOne)
    (hb : b ∈ rightSet epsilon y hEpsilon hY hOne) (g : ProjectiveGroup epsilon y) :
    a * g ≠ g * b := by sorry
