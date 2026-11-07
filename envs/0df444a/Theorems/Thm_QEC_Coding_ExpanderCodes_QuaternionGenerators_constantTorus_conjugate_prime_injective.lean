-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_constantTorus_conjugate_prime_injective
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.constantTorus_conjugate_prime_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:33:21.983785+00:00
-- url     : https://prove2.me/theorems/614b60f1-d95b-4e44-bcab-569d9af198d5
-- title:
--   Quaternion Generators: constant Torus conjugate prime injective
-- statement:
--   The Quaternion Generators construction uses the constant Torus conjugate prime injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L184-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L184-L196

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.constantTorus_conjugate_prime_injective (f : F →+* K) (epsilon : F)
    (y : K) (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) :
    Function.Injective (fun t : constantTorus f epsilon y =>
      (t : ProjectiveGroup (f epsilon) y) *
        projectivePrime (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne *
          (t : ProjectiveGroup (f epsilon) y)⁻¹) := by sorry
