-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticCoordinate_to_functionField
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticCoordinate_to_functionField
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:24:22.594395+00:00
-- url     : https://prove2.me/theorems/d6e6ccb5-bbdd-481c-8b83-a9f8f4f6be9c
-- title:
--   Cartwright Steger: arithmetic Coordinate to function Field
-- statement:
--   The Cartwright Steger construction uses the arithmetic Coordinate to function Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/SplitCoordinates.lean#L21-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/SplitCoordinates.lean#L21-L29

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_SplitCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticCoordinate_to_functionField
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    arithmeticRingToFunctionField P
        (cartwrightStegerOrderArithmeticCoordinate P r x p) =
      (functionFieldCyclicBasis P r).repr
        (cartwrightStegerOrderToCyclicAlgebra P r x) p := by sorry
