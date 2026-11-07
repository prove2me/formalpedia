-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusGL_pow_matrixRank
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusGL_pow_matrixRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:35.796206+00:00
-- url     : https://prove2.me/theorems/c08731a9-20a9-4b97-9647-7b53a4d05da8
-- title:
--   Cartwright Steger: frobenius GL pow matrix Rank
-- statement:
--   The rank-indexed matrix chosen for Frobenius has the same order relation
--   as the underlying finite-field automorphism.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L260-L279
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L260-L279

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusGL_pow_matrixRank (P : BasePrime) (r : Rank) :
    frobeniusGL P r ^ r.matrixRank = 1 := by sorry
