-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_constantTorus_conjugate_prime
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.constantTorus_conjugate_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:33:23.310321+00:00
-- url     : https://prove2.me/theorems/fe3e675c-b488-4226-81af-6a882c3476e6
-- title:
--   Quaternion Generators: constant Torus conjugate prime
-- statement:
--   The Quaternion Generators construction uses the constant Torus conjugate prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L165-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L165-L182

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.constantTorus_conjugate_prime (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (t : constantTorus f epsilon y) :
    (t : ProjectiveGroup (f epsilon) y) *
        projectivePrime (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne *
          (t : ProjectiveGroup (f epsilon) y)⁻¹ =
      projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon) *
        ((t : ProjectiveGroup (f epsilon) y) * projectiveBase (f epsilon) y hY hOne *
          (t : ProjectiveGroup (f epsilon) y)⁻¹) := by sorry
