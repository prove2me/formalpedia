-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCyclicGeneratorPGL_pow_matrixRank
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCyclicGeneratorPGL_pow_matrixRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:58:07.653579+00:00
-- url     : https://prove2.me/theorems/7677f5e0-9251-49bd-b03e-84e04652cb87
-- title:
--   Cartwright Steger: building Cyclic Generator PGL pow matrix Rank
-- statement:
--   The local cyclic element has projective order dividing the matrix rank,
--   because its rank-th power is the central scalar `1 + y`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L247-L268
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L247-L268

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCyclicGeneratorPGL_pow_matrixRank
    (P : BasePrime) (r : Rank) :
    buildingCyclicGeneratorPGL P r ^ r.matrixRank = 1 := by sorry
