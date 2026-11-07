-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingConstantPGLHom_map_baseUnit_eq_one
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstantPGLHom_map_baseUnit_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:57:59.462194+00:00
-- url     : https://prove2.me/theorems/fb77df93-d849-471a-a798-4513bdb83b8f
-- title:
--   Cartwright Steger: building Constant PGLHom map base Unit eq one
-- statement:
--   Base-field units act as scalar matrices and hence disappear after
--   projectivization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L336-L365
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L336-L365

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstantPGLHom_map_baseUnit_eq_one
    (P : BasePrime) (r : Rank) (a : (BaseField P)ˣ) :
    buildingConstantPGLHom P r
        (Units.map
          (algebraMap (BaseField P) (ConstantExtension P r)).toMonoidHom a) = 1 := by sorry
