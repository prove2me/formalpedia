-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_basis_mul_mem_arithmeticCyclicSpan
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.basis_mul_mem_arithmeticCyclicSpan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:22:29.574991+00:00
-- url     : https://prove2.me/theorems/2e730704-a2b4-4aa6-a952-08cdd05eb257
-- title:
--   Cartwright Steger: basis mul mem arithmetic Cyclic Span
-- statement:
--   The Cartwright Steger construction uses the basis mul mem arithmetic Cyclic Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L108-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L108-L179

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.basis_mul_mem_arithmeticCyclicSpan
    (P : BasePrime) (r : Rank)
    (p q : Fin r.matrixRank × Fin r.matrixRank) :
    functionFieldCyclicBasisVector P r p *
        functionFieldCyclicBasisVector P r q ∈
      arithmeticCyclicSpan P r := by sorry
