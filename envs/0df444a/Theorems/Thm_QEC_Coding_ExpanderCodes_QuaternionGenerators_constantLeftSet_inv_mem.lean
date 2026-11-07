-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_constantLeftSet_inv_mem
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.constantLeftSet_inv_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:35:14.040539+00:00
-- url     : https://prove2.me/theorems/1ac5453c-62df-426f-adca-e91ba563ff9e
-- title:
--   Quaternion Generators: constant Left Set inv mem
-- statement:
--   The Quaternion Generators construction uses the constant Left Set inv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L221-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L221-L226

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.constantLeftSet_inv_mem (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    {g : ProjectiveGroup (f epsilon) y} (hg : g ∈ constantLeftSet f epsilon y hY hOne) :
    g⁻¹ ∈ constantLeftSet f epsilon y hY hOne := by sorry
