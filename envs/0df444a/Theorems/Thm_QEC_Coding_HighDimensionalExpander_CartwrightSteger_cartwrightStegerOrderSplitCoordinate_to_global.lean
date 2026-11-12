-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerOrderSplitCoordinate_to_global
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerOrderSplitCoordinate_to_global
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:24:19.162862+00:00
-- url     : https://prove2.me/theorems/b32d98c0-886e-4e48-9178-3b79171d3c20
-- title:
--   Cartwright Steger: cartwright Steger Order Split Coordinate to global
-- statement:
--   The Cartwright Steger construction uses the cartwright Steger Order Split Coordinate to global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/SplitCoordinates.lean#L43-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/SplitCoordinates.lean#L43-L98

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_SplitCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
set_option maxHeartbeats 800000

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerOrderSplitCoordinate_to_global
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r) :
    (cartwrightStegerOrderSplitCoordinate P r x).map
        (constantArithmeticToSplittingFunctionField P r) = x := by sorry
