-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:43:56.060002+00:00
-- url     : https://prove2.me/theorems/319c9d0a-4f4f-48a8-9809-b402f6124da1
-- title:
--   Cartwright Steger: constant Unit Matrix val
-- statement:
--   The Cartwright Steger construction uses the constant Unit Matrix val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L589-L594
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L589-L594

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val (P : BasePrime) (r : Rank)
    (u : Units (ConstantExtension P r)) :
    (constantUnitMatrix P r u :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) = constantMatrix P r u := by sorry

attribute [defeq] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
