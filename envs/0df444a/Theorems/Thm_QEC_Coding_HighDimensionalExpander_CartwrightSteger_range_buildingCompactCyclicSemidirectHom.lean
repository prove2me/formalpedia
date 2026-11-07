-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_range_buildingCompactCyclicSemidirectHom
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.range_buildingCompactCyclicSemidirectHom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:01:39.651678+00:00
-- url     : https://prove2.me/theorems/6d482f21-04ae-464f-bb4b-8934cd9ced5e
-- title:
--   Cartwright Steger: range building Compact Cyclic Semidirect Hom
-- statement:
--   The compact cyclic subgroup is exactly the image of the Frobenius
--   semidirect product, not merely a closure with unspecified elements.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L619-L640
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L619-L640

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.range_buildingCompactCyclicSemidirectHom
    (P : BasePrime) (r : Rank) :
    (buildingCompactCyclicSemidirectHom P r).range =
      BuildingCompactCyclicSubgroup P r := by sorry
