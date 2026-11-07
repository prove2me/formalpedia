-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_constantSets_total_nonconjugacy
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.constantSets_total_nonconjugacy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:35:20.521543+00:00
-- url     : https://prove2.me/theorems/fabc0bca-5ac3-406b-9f85-961ef120bc1e
-- title:
--   Quaternion Generators: constant Sets total nonconjugacy
-- statement:
--   The Quaternion Generators construction uses the constant Sets total nonconjugacy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L236-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L236-L244

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.constantSets_total_nonconjugacy (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) {a b : ProjectiveGroup (f epsilon) y}
    (ha : a ∈ constantLeftSet f epsilon y hY hOne)
    (hb : b ∈ constantRightSet f epsilon y hEpsilon hY hOne)
    (g : ProjectiveGroup (f epsilon) y) : a * g ≠ g * b := by sorry
