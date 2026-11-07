-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCyclicGeneratorPGL_pow_conj_constant
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCyclicGeneratorPGL_pow_conj_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:01:17.141381+00:00
-- url     : https://prove2.me/theorems/bf52d6a4-bb80-471f-9fac-02ffc283f24b
-- title:
--   Cartwright Steger: building Cyclic Generator PGL pow conj constant
-- statement:
--   Natural-power specialization of cyclic conjugation, used for the
--   canonical exponents `0 ≤ j < d`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L180-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L180-L189

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCyclicGeneratorPGL_pow_conj_constant
    (P : BasePrime) (r : Rank) (j : ℕ)
    (u : (ConstantExtension P r)ˣ) :
    buildingCyclicGeneratorPGL P r ^ j *
        buildingConstantPGLHom P r u *
        (buildingCyclicGeneratorPGL P r ^ j)⁻¹ =
      buildingConstantPGLHom P r
        ((constantFrobeniusUnitEquiv P r ^ j) u) := by sorry
