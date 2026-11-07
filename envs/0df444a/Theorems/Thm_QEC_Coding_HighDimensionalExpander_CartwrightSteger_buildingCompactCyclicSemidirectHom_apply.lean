-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCompactCyclicSemidirectHom_apply
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCompactCyclicSemidirectHom_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:58:00.821191+00:00
-- url     : https://prove2.me/theorems/01c2c71e-1444-4eda-8e64-e9a89a2af1e2
-- title:
--   Cartwright Steger: building Compact Cyclic Semidirect Hom apply
-- statement:
--   The Cartwright Steger construction uses the building Compact Cyclic Semidirect Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L237-L243
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L237-L243

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCompactCyclicSemidirectHom_apply
    (P : BasePrime) (r : Rank)
    (x : BuildingCompactCyclicSemidirect P r) :
    buildingCompactCyclicSemidirectHom P r x =
      buildingConstantPGLHom P r x.left *
        buildingCyclicGeneratorPGL P r ^ x.right.toAdd := by sorry

attribute [defeq] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCompactCyclicSemidirectHom_apply
