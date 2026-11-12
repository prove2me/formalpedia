-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_orderUnitLattice_lift_of_buildingLattice
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_orderUnitLattice_lift_of_buildingLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:28:34.369063+00:00
-- url     : https://prove2.me/theorems/4978e267-1304-4901-99ae-aa86f1ccd400
-- title:
--   Cartwright Steger: exists order Unit Lattice lift of building Lattice
-- statement:
--   The Cartwright Steger construction uses the exists order Unit Lattice lift of building Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/LatticeBridge.lean#L100-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/LatticeBridge.lean#L100-L113

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_orderUnitLattice_lift_of_buildingLattice
    (P : BasePrime) (r : Rank)
    (g : BuildingCartwrightStegerLattice P r) :
    ∃ u : (CartwrightStegerOrder P r)ˣ,
      u ∈ CartwrightStegerOrderUnitLattice P r ∧
      orderUnitToBuildingPGL P r u = g := by sorry
