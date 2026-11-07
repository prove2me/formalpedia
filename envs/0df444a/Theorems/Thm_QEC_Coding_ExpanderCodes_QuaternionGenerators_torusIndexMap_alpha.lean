-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_torusIndexMap_alpha
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.torusIndexMap_alpha
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:33:38.972202+00:00
-- url     : https://prove2.me/theorems/27105fdf-74ea-4b16-935d-14cf7f115138
-- title:
--   Quaternion Generators: torus Index Map alpha
-- statement:
--   The Quaternion Generators construction uses the torus Index Map alpha property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorusIndex.lean#L93-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorusIndex.lean#L93-L101

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.torusIndexMap_alpha (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    torusIndexMap f epsilon y hTwoF hOne hTwo (torusIndexAlpha epsilon hEpsilon) =
      projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon) := by sorry
