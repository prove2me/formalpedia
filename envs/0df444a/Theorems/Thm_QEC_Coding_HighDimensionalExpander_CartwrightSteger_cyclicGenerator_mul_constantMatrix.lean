-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGenerator_mul_constantMatrix
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGenerator_mul_constantMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:52:33.841233+00:00
-- url     : https://prove2.me/theorems/54ae34dc-c52c-4c10-9cf8-004d33433f2a
-- title:
--   Cartwright Steger: cyclic Generator mul constant Matrix
-- statement:
--   The second defining relation of the cyclic algebra.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L339-L363
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L339-L363

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGenerator_mul_constantMatrix (P : BasePrime) (r : Rank)
    (c : ConstantExtension P r) :
    cyclicGeneratorMatrix P r * constantMatrix P r c =
      constantMatrix P r (constantFrobenius P r c) *
        cyclicGeneratorMatrix P r := by sorry
