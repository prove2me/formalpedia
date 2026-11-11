-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_one_mem_arithmeticCyclicSpan
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.one_mem_arithmeticCyclicSpan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:54:30.234565+00:00
-- url     : https://prove2.me/theorems/8b6caf48-7245-4aad-8557-3dfc63c24e6f
-- title:
--   Cartwright Steger: one mem arithmetic Cyclic Span
-- statement:
--   The Cartwright Steger construction uses the one mem arithmetic Cyclic Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L211-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L211-L225

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.one_mem_arithmeticCyclicSpan (P : BasePrime) (r : Rank) :
    (1 : CyclicAlgebra P r) ∈ arithmeticCyclicSpan P r := by sorry
