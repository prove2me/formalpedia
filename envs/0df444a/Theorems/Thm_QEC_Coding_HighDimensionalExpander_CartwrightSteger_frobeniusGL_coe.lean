-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusGL_coe
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusGL_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:49:31.346725+00:00
-- url     : https://prove2.me/theorems/1e2710ef-420d-4a1a-a28d-c5371479c424
-- title:
--   Cartwright Steger: frobenius GL coe
-- statement:
--   The matrix selected for Frobenius is literally the matrix of the
--   constant-field Frobenius in the fixed basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L283-L306
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L283-L306

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusGL_coe (P : BasePrime) (r : Rank) :
    (frobeniusGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) =
      LinearMap.toMatrix (constantBasis P r) (constantBasis P r)
        (constantFrobenius P r).toLinearEquiv.toLinearMap := by sorry
