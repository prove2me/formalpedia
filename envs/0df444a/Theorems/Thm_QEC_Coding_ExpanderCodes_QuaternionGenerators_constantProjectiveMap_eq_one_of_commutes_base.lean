-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_constantProjectiveMap_eq_one_of_commutes_base
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.constantProjectiveMap_eq_one_of_commutes_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:33:18.694855+00:00
-- url     : https://prove2.me/theorems/6319e891-c3f6-4a82-bace-d9e85396f646
-- title:
--   Quaternion Generators: constant Projective Map eq one of commutes base
-- statement:
--   A constant torus element stabilizing the first generator is projectively
--   trivial. This proves freeness of the orbit rather than assuming its size.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L61-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L61-L108

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.constantProjectiveMap_eq_one_of_commutes_base
    (f : F →+* K) (epsilon : F) (y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (a : (QuadraticAlgebra F epsilon 0)ˣ)
    (hCommute : constantProjectiveMap f epsilon y a * projectiveBase (f epsilon) y hY hOne =
      projectiveBase (f epsilon) y hY hOne * constantProjectiveMap f epsilon y a) :
    constantProjectiveMap f epsilon y a = 1 := by sorry
