-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderUnitLattice_to_global
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_orderUnitLattice_to_global
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:28:20.052626+00:00
-- url     : https://prove2.me/theorems/a4b8d941-e0c6-40db-be19-bc4d66f1e1b6
-- title:
--   Cartwright Steger: map order Unit Lattice to global
-- statement:
--   The Cartwright Steger construction uses the map order Unit Lattice to global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/LatticeBridge.lean#L69-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/LatticeBridge.lean#L69-L82

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_orderUnitLattice_to_global
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrderUnitLattice P r).map (orderUnitToGlobalGL P r) =
      CartwrightStegerMatrixGroup P r := by sorry
