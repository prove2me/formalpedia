-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingConstantPGLHom_eq_one_of_constantFrobeniusUnitEquiv_eq
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstantPGLHom_eq_one_of_constantFrobeniusUnitEquiv_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:00:53.85695+00:00
-- url     : https://prove2.me/theorems/148a01b7-b3df-4057-9d86-0aaaa79c597b
-- title:
--   Cartwright Steger: building Constant PGLHom eq one of constant Frobenius Unit Equiv eq
-- statement:
--   Consequently every Frobenius-fixed represented constant unit is the
--   projective identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L369-L375
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L369-L375

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstantPGLHom_eq_one_of_constantFrobeniusUnitEquiv_eq
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (hu : constantFrobeniusUnitEquiv P r u = u) :
    buildingConstantPGLHom P r u = 1 := by sorry
