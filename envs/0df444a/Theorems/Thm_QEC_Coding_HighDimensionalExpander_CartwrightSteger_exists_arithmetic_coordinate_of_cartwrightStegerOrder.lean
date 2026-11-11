-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_arithmetic_coordinate_of_cartwrightStegerOrder
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_arithmetic_coordinate_of_cartwrightStegerOrder
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T03:54:26.319976+00:00
-- url     : https://prove2.me/theorems/e91ba8ed-7ae6-4b44-8614-85e81d95d9cc
-- title:
--   Cartwright Steger: exists arithmetic coordinate of cartwright Steger Order
-- statement:
--   Each function-field cyclic coordinate of an order element is the image
--   of an arithmetic-ring coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L364-L392
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L364-L392

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_arithmetic_coordinate_of_cartwrightStegerOrder
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    ∃ a : ArithmeticRing P,
      arithmeticRingToFunctionField P a =
        (functionFieldCyclicBasis P r).repr
          (cartwrightStegerOrderToCyclicAlgebra P r x) p := by sorry
