-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_constantTorus_conjugate_base_injective
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.constantTorus_conjugate_base_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:33:22.073497+00:00
-- url     : https://prove2.me/theorems/d6c14283-b574-4762-8bf6-5f2ceac79048
-- title:
--   Quaternion Generators: constant Torus conjugate base injective
-- statement:
--   The Quaternion Generators construction uses the constant Torus conjugate base injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L110-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L110-L128

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.constantTorus_conjugate_base_injective (f : F →+* K) (epsilon : F)
    (y : K) (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) :
    Function.Injective (fun t : constantTorus f epsilon y =>
      (t : ProjectiveGroup (f epsilon) y) * projectiveBase (f epsilon) y hY hOne *
        (t : ProjectiveGroup (f epsilon) y)⁻¹) := by sorry
