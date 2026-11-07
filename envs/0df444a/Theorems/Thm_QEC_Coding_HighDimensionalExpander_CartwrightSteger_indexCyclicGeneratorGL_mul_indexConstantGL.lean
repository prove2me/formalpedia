-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_mul_indexConstantGL
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_mul_indexConstantGL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:40:29.661098+00:00
-- url     : https://prove2.me/theorems/68b06938-f345-4d46-9672-8682cab2ffd1
-- title:
--   Cartwright Steger: index Cyclic Generator GL mul index Constant GL
-- statement:
--   Bundled form of the proved skew relation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSplitting.lean#L248-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSplitting.lean#L248-L257

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_mul_indexConstantGL
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    indexCyclicGeneratorGL P r level * indexConstantGL P r level u =
      indexConstantGL P r level
          (indexConstantFrobeniusUnit P r u) *
        indexCyclicGeneratorGL P r level := by sorry
