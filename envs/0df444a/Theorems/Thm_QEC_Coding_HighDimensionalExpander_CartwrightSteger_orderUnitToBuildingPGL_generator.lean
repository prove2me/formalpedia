-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToBuildingPGL_generator
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToBuildingPGL_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:29:07.862332+00:00
-- url     : https://prove2.me/theorems/0a5467fe-90c0-43d7-b299-cd7662ac96e4
-- title:
--   Cartwright Steger: order Unit To Building PGL generator
-- statement:
--   The Cartwright Steger construction uses the order Unit To Building PGL generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/LatticeBridge.lean#L54-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/LatticeBridge.lean#L54-L60

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToBuildingPGL_generator
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    orderUnitToBuildingPGL P r (cartwrightStegerOrderUnitGenerator P r x) =
      buildingCartwrightStegerGenerator P r x := by sorry
