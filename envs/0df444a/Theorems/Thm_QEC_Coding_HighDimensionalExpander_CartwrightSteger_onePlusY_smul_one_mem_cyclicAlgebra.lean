-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_onePlusY_smul_one_mem_cyclicAlgebra
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.onePlusY_smul_one_mem_cyclicAlgebra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:29:16.513892+00:00
-- url     : https://prove2.me/theorems/799e03c0-5225-4a2b-97e9-ffdd6a3fddd2
-- title:
--   Cartwright Steger: one Plus Y smul one mem cyclic Algebra
-- statement:
--   The central base function `1 + y` acts by a scalar matrix in the cyclic
--   algebra, as follows from the proved power relation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L643-L650
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L643-L650

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.onePlusY_smul_one_mem_cyclicAlgebra (P : BasePrime) (r : Rank) :
    (onePlusY P r) •
        (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) ∈
      CyclicAlgebra P r := by sorry
