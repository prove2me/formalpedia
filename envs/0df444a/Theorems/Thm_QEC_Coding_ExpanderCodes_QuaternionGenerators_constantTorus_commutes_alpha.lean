-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_constantTorus_commutes_alpha
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.constantTorus_commutes_alpha
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:33:31.546854+00:00
-- url     : https://prove2.me/theorems/d087b7e6-297d-49db-ad80-de46dfc99349
-- title:
--   Quaternion Generators: constant Torus commutes alpha
-- statement:
--   Every constant torus element commutes with the quadratic unit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L149-L163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L149-L163

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.constantTorus_commutes_alpha (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (t : constantTorus f epsilon y) :
    (t : ProjectiveGroup (f epsilon) y) *
        projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon) =
      projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon) * t := by sorry
