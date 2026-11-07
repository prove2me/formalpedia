-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_indexedLeft_injective
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.indexedLeft_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:33:42.575603+00:00
-- url     : https://prove2.me/theorems/999cb3d2-6c72-4ae1-8ca8-5d54dc9f8538
-- title:
--   Quaternion Generators: indexed Left injective
-- statement:
--   The Quaternion Generators construction uses the indexed Left injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorusIndex.lean#L119-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorusIndex.lean#L119-L124

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.indexedLeft_injective (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    Function.Injective (indexedLeft f epsilon y hTwoF hY hOne hTwo) := by sorry
