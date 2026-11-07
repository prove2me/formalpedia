-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_indexedRight_inverse
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.indexedRight_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:33:44.515725+00:00
-- url     : https://prove2.me/theorems/0bb69f93-13ab-4f62-91d9-19773549e7e7
-- title:
--   Quaternion Generators: indexed Right inverse
-- statement:
--   The Quaternion Generators construction uses the indexed Right inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorusIndex.lean#L154-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorusIndex.lean#L154-L162

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.indexedRight_inverse (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) (t : TorusIndex epsilon) :
    indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo t =
      (indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo t)⁻¹ := by sorry
