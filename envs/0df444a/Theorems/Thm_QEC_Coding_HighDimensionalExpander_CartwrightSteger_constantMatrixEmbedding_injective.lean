-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantMatrixEmbedding_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantMatrixEmbedding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:54:48.535203+00:00
-- url     : https://prove2.me/theorems/74fe8e00-1528-4bae-87c0-13e969a70193
-- title:
--   Cartwright Steger: constant Matrix Embedding injective
-- statement:
--   The Cartwright Steger construction uses the constant Matrix Embedding injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L213-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L213-L220

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantMatrixEmbedding_injective (P : BasePrime) (r : Rank) :
    Function.Injective (constantMatrixEmbedding P r) := by sorry
