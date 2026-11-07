-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_torusIndexMap_injective
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.torusIndexMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:35:25.836209+00:00
-- url     : https://prove2.me/theorems/d065c82c-67af-4612-bcac-8d4d9e853ec8
-- title:
--   Quaternion Generators: torus Index Map injective
-- statement:
--   The Quaternion Generators construction uses the torus Index Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorusIndex.lean#L61-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorusIndex.lean#L61-L64

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.torusIndexMap_injective (f : F →+* K) (epsilon : F) (y : K)
    (hTwoF : (2 : F) ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    Function.Injective (torusIndexMap f epsilon y hTwoF hOne hTwo) := by sorry
