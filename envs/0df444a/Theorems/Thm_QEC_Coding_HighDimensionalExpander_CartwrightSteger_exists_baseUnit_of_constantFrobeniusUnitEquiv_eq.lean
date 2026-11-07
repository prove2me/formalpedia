-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_baseUnit_of_constantFrobeniusUnitEquiv_eq
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_baseUnit_of_constantFrobeniusUnitEquiv_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:00:48.362078+00:00
-- url     : https://prove2.me/theorems/d40425e3-a7ad-47b8-8226-057eeab85aa4
-- title:
--   Cartwright Steger: exists base Unit of constant Frobenius Unit Equiv eq
-- statement:
--   A unit fixed by arithmetic Frobenius is not merely a fixed field
--   element: it is the image of an actual base-field unit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L316-L332
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L316-L332

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_baseUnit_of_constantFrobeniusUnitEquiv_eq
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (hu : constantFrobeniusUnitEquiv P r u = u) :
    ∃ a : (BaseField P)ˣ,
      Units.map (algebraMap (BaseField P) (ConstantExtension P r)).toMonoidHom a = u := by sorry
