-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_indexedLeft_inverse
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.indexedLeft_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:33:44.623194+00:00
-- url     : https://prove2.me/theorems/4b2a2750-bc51-4c96-84df-eec0de12c36a
-- title:
--   Quaternion Generators: indexed Left inverse
-- statement:
--   The Quaternion Generators construction uses the indexed Left inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorusIndex.lean#L137-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorusIndex.lean#L137-L152

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.indexedLeft_inverse (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) (t : TorusIndex epsilon) :
    indexedLeft f epsilon y hTwoF hY hOne hTwo (indexedLeftInverse epsilon hEpsilon t) =
      (indexedLeft f epsilon y hTwoF hY hOne hTwo t)⁻¹ := by sorry
