-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_CyclicCartwrightStegerLattice_to_building
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_CyclicCartwrightStegerLattice_to_building
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:47:35.7642+00:00
-- url     : https://prove2.me/theorems/f458f77e-9b67-464d-8e4b-1e9821922320
-- title:
--   Cartwright Steger: map Cyclic Cartwright Steger Lattice to building
-- statement:
--   The Cartwright Steger construction uses the map Cyclic Cartwright Steger Lattice to building property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/GlobalBuildingLattice.lean#L171-L187
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/GlobalBuildingLattice.lean#L171-L187

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_GlobalBuildingLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_CyclicCartwrightStegerLattice_to_building
    (P : BasePrime) (r : Rank) :
    (CyclicCartwrightStegerLattice P r).map
        (cyclicUnitToBuildingPGL P r) =
      BuildingCartwrightStegerLattice P r := by sorry
