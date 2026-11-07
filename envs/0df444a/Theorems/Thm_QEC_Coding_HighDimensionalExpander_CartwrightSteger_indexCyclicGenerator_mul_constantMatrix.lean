-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGenerator_mul_constantMatrix
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGenerator_mul_constantMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:40:25.133206+00:00
-- url     : https://prove2.me/theorems/50a8a1b7-ccc1-47ce-b9b7-927da53dbf14
-- title:
--   Cartwright Steger: index Cyclic Generator mul constant Matrix
-- statement:
--   The second cyclic-algebra relation at the actual selected place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSplitting.lean#L167-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSplitting.lean#L167-L194

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGenerator_mul_constantMatrix
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ConstantExtension P r) :
    indexCyclicGeneratorMatrix P r level *
        indexConstantMatrix P r level c =
      indexConstantMatrix P r level (constantFrobenius P r c) *
        indexCyclicGeneratorMatrix P r level := by sorry
