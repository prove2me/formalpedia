-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorInverse_mem_arithmeticCyclicSpan
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGeneratorInverse_mem_arithmeticCyclicSpan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:23:13.304145+00:00
-- url     : https://prove2.me/theorems/49bc7973-cb64-48eb-87d1-931af461f1fe
-- title:
--   Cartwright Steger: cyclic Generator Inverse mem arithmetic Cyclic Span
-- statement:
--   The Cartwright Steger construction uses the cyclic Generator Inverse mem arithmetic Cyclic Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L287-L320
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L287-L320

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorInverseMatrix_mem_cyclicAlgebra

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGeneratorInverse_mem_arithmeticCyclicSpan
    (P : BasePrime) (r : Rank) :
    (⟨cyclicGeneratorInverseMatrix P r,
      cyclicGeneratorInverseMatrix_mem_cyclicAlgebra P r⟩ : CyclicAlgebra P r) ∈
      arithmeticCyclicSpan P r := by sorry
