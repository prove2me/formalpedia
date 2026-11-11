-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerOrderToCyclic_mem_arithmeticCyclicSpan
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerOrderToCyclic_mem_arithmeticCyclicSpan
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T03:54:30.822725+00:00
-- url     : https://prove2.me/theorems/e1a82712-2cd3-4adb-b837-293c17b9ceb4
-- title:
--   Cartwright Steger: cartwright Steger Order To Cyclic mem arithmetic Cyclic Span
-- statement:
--   Every element of the arithmetic Cartwright--Steger order has arithmetic
--   coordinates in the explicit cyclic basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L324-L360
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L324-L360

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerOrderToCyclic_mem_arithmeticCyclicSpan
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r) :
    cartwrightStegerOrderToCyclicAlgebra P r x ∈
      arithmeticCyclicSpan P r := by sorry
