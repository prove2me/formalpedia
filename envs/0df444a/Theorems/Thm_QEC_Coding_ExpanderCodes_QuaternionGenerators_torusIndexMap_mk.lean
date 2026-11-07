-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_torusIndexMap_mk
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.torusIndexMap_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:33:56.002606+00:00
-- url     : https://prove2.me/theorems/4b515795-2741-4a39-b371-a9542ba82797
-- title:
--   Quaternion Generators: torus Index Map mk
-- statement:
--   The Quaternion Generators construction uses the torus Index Map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorusIndex.lean#L55-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorusIndex.lean#L55-L59

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.torusIndexMap_mk (f : F →+* K) (epsilon : F) (y : K)
    (hTwoF : (2 : F) ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (a : (QuadraticAlgebra F epsilon 0)ˣ) :
    torusIndexMap f epsilon y hTwoF hOne hTwo (QuotientGroup.mk a) =
      constantProjectiveMap f epsilon y a := by sorry

attribute [defeq] QEC.Coding.ExpanderCodes.QuaternionGenerators.torusIndexMap_mk
