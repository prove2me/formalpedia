-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGenerator_pow_matrixRank
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGenerator_pow_matrixRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:57.505863+00:00
-- url     : https://prove2.me/theorems/960154ba-70e9-4326-9748-8c5e2ca2824d
-- title:
--   Cartwright Steger: cyclic Generator pow matrix Rank
-- statement:
--   The first defining relation of the cyclic algebra, checked from the
--   rank-three and rank-four matrices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L166-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L166-L172

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGenerator_pow_matrixRank (P : BasePrime) (r : Rank) :
    cyclicGeneratorMatrix P r ^ r.matrixRank =
      (onePlusY P r) • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) := by sorry
