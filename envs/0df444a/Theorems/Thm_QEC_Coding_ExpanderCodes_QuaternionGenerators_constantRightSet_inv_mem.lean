-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_constantRightSet_inv_mem
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.constantRightSet_inv_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:35:17.714203+00:00
-- url     : https://prove2.me/theorems/e6a93fef-ae7d-4007-a82d-664392780a41
-- title:
--   Quaternion Generators: constant Right Set inv mem
-- statement:
--   The Quaternion Generators construction uses the constant Right Set inv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L228-L234
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L228-L234

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.constantRightSet_inv_mem (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    {g : ProjectiveGroup (f epsilon) y}
    (hg : g ∈ constantRightSet f epsilon y hEpsilon hY hOne) :
    g⁻¹ ∈ constantRightSet f epsilon y hEpsilon hY hOne := by sorry
