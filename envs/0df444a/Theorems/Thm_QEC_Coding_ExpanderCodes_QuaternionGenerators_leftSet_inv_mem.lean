-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_leftSet_inv_mem
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.leftSet_inv_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:30:47.875955+00:00
-- url     : https://prove2.me/theorems/3214365f-9cb7-46f1-847f-df3c3bf0e17a
-- title:
--   Quaternion Generators: left Set inv mem
-- statement:
--   The Quaternion Generators construction uses the left Set inv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionCayleySets.lean#L109-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionCayleySets.lean#L109-L114

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionCayleySets
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.leftSet_inv_mem (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) {g : ProjectiveGroup epsilon y}
    (hg : g ∈ leftSet epsilon y hEpsilon hY hOne) :
    g⁻¹ ∈ leftSet epsilon y hEpsilon hY hOne := by sorry
