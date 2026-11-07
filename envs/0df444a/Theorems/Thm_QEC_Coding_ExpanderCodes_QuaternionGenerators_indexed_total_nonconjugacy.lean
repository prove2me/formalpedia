-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_indexed_total_nonconjugacy
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.indexed_total_nonconjugacy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:33:58.33028+00:00
-- url     : https://prove2.me/theorems/c4aff0fa-d07a-4888-aacd-5615697f2cc7
-- title:
--   Quaternion Generators: indexed total nonconjugacy
-- statement:
--   The Quaternion Generators construction uses the indexed total nonconjugacy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorusIndex.lean#L164-L171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorusIndex.lean#L164-L171

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.indexed_total_nonconjugacy (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (a b : TorusIndex epsilon) (g : ProjectiveGroup (f epsilon) y) :
    indexedLeft f epsilon y hTwoF hY hOne hTwo a * g ≠
      g * indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo b := by sorry
