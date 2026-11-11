-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantCyclicMonomial_mem_arithmeticCyclicSpan
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantCyclicMonomial_mem_arithmeticCyclicSpan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:53:45.316745+00:00
-- url     : https://prove2.me/theorems/422938cc-be10-4b01-8c1c-8e9e5f48782c
-- title:
--   Cartwright Steger: constant Cyclic Monomial mem arithmetic Cyclic Span
-- statement:
--   The Cartwright Steger construction uses the constant Cyclic Monomial mem arithmetic Cyclic Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L44-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L44-L96

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantMatrix_mem_cyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorMatrix_mem_cyclicAlgebra

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantCyclicMonomial_mem_arithmeticCyclicSpan
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r)
    (k : ℕ) (hk : k < r.matrixRank) :
    (⟨constantMatrix P r c * cyclicGeneratorMatrix P r ^ k,
      (CyclicAlgebra P r).mul_mem
        (constantMatrix_mem_cyclicAlgebra P r c)
        ((CyclicAlgebra P r).pow_mem
          (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) k)⟩ :
      CyclicAlgebra P r) ∈ arithmeticCyclicSpan P r := by sorry
