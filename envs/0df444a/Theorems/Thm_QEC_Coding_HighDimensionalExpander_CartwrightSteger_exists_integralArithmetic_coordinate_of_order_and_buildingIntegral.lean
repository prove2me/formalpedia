-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_integralArithmetic_coordinate_of_order_and_buildingIntegral
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_integralArithmetic_coordinate_of_order_and_buildingIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:24:16.197987+00:00
-- url     : https://prove2.me/theorems/26e7fb66-f4a1-40a5-b332-abefbdd5c616
-- title:
--   Cartwright Steger: exists integral Arithmetic coordinate of order and building Integral
-- statement:
--   Coordinatewise form of the arithmetic/building intersection for an
--   actual order element.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L396-L418
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L396-L418

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_integralArithmetic_coordinate_of_order_and_buildingIntegral
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r)
    (hlocal : ∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r x))
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    ∃ a : IntegralArithmeticRing P,
      integralArithmeticToFunctionField P a =
        (functionFieldCyclicBasis P r).repr
          (cartwrightStegerOrderToCyclicAlgebra P r x) p := by sorry
