-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderUnitLattice_to_building
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_orderUnitLattice_to_building
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:28:42.683475+00:00
-- url     : https://prove2.me/theorems/241add6d-d346-4dc7-9580-9f90201a4dd3
-- title:
--   Cartwright Steger: map order Unit Lattice to building
-- statement:
--   The Cartwright Steger construction uses the map order Unit Lattice to building property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/LatticeBridge.lean#L84-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/LatticeBridge.lean#L84-L98

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_orderUnitLattice_to_building
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrderUnitLattice P r).map
        (orderUnitToBuildingPGL P r) =
      BuildingCartwrightStegerLattice P r := by sorry
