-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorMatrix_mem_cyclicAlgebra
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGeneratorMatrix_mem_cyclicAlgebra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:52:12.923644+00:00
-- url     : https://prove2.me/theorems/ff790af5-827a-40e8-b2eb-c57afdc1bdca
-- title:
--   Cartwright Steger: cyclic Generator Matrix mem cyclic Algebra
-- statement:
--   The Cartwright Steger construction uses the cyclic Generator Matrix mem cyclic Algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L382-L385
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L382-L385

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGeneratorMatrix_mem_cyclicAlgebra (P : BasePrime) (r : Rank) :
    cyclicGeneratorMatrix P r ∈ CyclicAlgebra P r := by sorry
