-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_functionFieldEmbedding_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.functionFieldEmbedding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:28:38.980125+00:00
-- url     : https://prove2.me/theorems/40d39531-4342-4f66-a6a9-3265abaec044
-- title:
--   Cartwright Steger: function Field Embedding injective
-- statement:
--   The Cartwright Steger construction uses the function Field Embedding injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L38-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L38-L40

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.functionFieldEmbedding_injective (P : BasePrime) (r : Rank) :
    Function.Injective (functionFieldEmbedding P r) := by sorry
