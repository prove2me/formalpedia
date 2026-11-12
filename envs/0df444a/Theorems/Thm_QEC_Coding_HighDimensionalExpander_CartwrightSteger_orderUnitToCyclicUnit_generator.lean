-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToCyclicUnit_generator
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToCyclicUnit_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:29:05.093237+00:00
-- url     : https://prove2.me/theorems/c075b84f-bdb0-432e-a62d-4f8767559cb3
-- title:
--   Cartwright Steger: order Unit To Cyclic Unit generator
-- statement:
--   The Cartwright Steger construction uses the order Unit To Cyclic Unit generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/LatticeBridge.lean#L38-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/LatticeBridge.lean#L38-L43

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToCyclicUnit_generator
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    orderUnitToCyclicUnit P r (cartwrightStegerOrderUnitGenerator P r x) =
      cartwrightStegerGeneratorCyclicUnit P r x := by sorry
