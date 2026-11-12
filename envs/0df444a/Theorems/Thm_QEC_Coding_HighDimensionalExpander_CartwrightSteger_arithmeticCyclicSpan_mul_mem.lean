-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticCyclicSpan_mul_mem
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticCyclicSpan_mul_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:22:20.56729+00:00
-- url     : https://prove2.me/theorems/d724ecb5-58b5-4de0-a826-7237d6f9cddd
-- title:
--   Cartwright Steger: arithmetic Cyclic Span mul mem
-- statement:
--   The Cartwright Steger construction uses the arithmetic Cyclic Span mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L181-L209
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L181-L209

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticCyclicSpan_mul_mem
    (P : BasePrime) (r : Rank) (x y : CyclicAlgebra P r)
    (hx : x ∈ arithmeticCyclicSpan P r)
    (hy : y ∈ arithmeticCyclicSpan P r) :
    x * y ∈ arithmeticCyclicSpan P r := by sorry
