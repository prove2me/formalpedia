-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantMatrixEmbedding_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantMatrixEmbedding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:42:56.650488+00:00
-- url     : https://prove2.me/theorems/718c32e2-ae0f-47cd-9705-56ee88359569
-- title:
--   Cartwright Steger: index Constant Matrix Embedding injective
-- statement:
--   The Cartwright Steger construction uses the index Constant Matrix Embedding injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSplitting.lean#L71-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSplitting.lean#L71-L79

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantMatrixEmbedding_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective (indexConstantMatrixEmbedding P r level) := by sorry
