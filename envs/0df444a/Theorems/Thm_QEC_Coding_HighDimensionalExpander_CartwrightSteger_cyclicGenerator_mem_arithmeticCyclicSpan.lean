-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGenerator_mem_arithmeticCyclicSpan
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGenerator_mem_arithmeticCyclicSpan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:22:45.893507+00:00
-- url     : https://prove2.me/theorems/159e5d28-e71d-43ea-b80d-a8f4eaa6f626
-- title:
--   Cartwright Steger: cyclic Generator mem arithmetic Cyclic Span
-- statement:
--   The Cartwright Steger construction uses the cyclic Generator mem arithmetic Cyclic Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L265-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L265-L285

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorMatrix_mem_cyclicAlgebra

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGenerator_mem_arithmeticCyclicSpan
    (P : BasePrime) (r : Rank) :
    (⟨cyclicGeneratorMatrix P r,
      cyclicGeneratorMatrix_mem_cyclicAlgebra P r⟩ : CyclicAlgebra P r) ∈
      arithmeticCyclicSpan P r := by sorry
