-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectiveAlpha_mem_constantTorus
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveAlpha_mem_constantTorus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:33:23.853108+00:00
-- url     : https://prove2.me/theorems/1048c544-196f-41ef-86f1-fbb6a799a0df
-- title:
--   Quaternion Generators: projective Alpha mem constant Torus
-- statement:
--   The Quaternion Generators construction uses the projective Alpha mem constant Torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L27-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L27-L34

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveAlpha_mem_constantTorus (f : F →+* K) (epsilon : F)
    (y : K) (hEpsilon : epsilon ≠ 0) :
    projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon) ∈
      constantTorus f epsilon y := by sorry
