-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToGlobalGL_generator
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToGlobalGL_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:28:10.447332+00:00
-- url     : https://prove2.me/theorems/7826962c-73b6-44b5-8fd4-15bb5cb216fc
-- title:
--   Cartwright Steger: order Unit To Global GL generator
-- statement:
--   The Cartwright Steger construction uses the order Unit To Global GL generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/LatticeBridge.lean#L45-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/LatticeBridge.lean#L45-L52

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToGlobalGL_generator
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    orderUnitToGlobalGL P r (cartwrightStegerOrderUnitGenerator P r x) =
      cartwrightStegerGenerator P r x := by sorry
