-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_zpowers_constantFrobenius_eq_top
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.zpowers_constantFrobenius_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:59.235096+00:00
-- url     : https://prove2.me/theorems/04dacef6-c9c9-485a-b125-1c3f4657916c
-- title:
--   Cartwright Steger: zpowers constant Frobenius eq top
-- statement:
--   The arithmetic Frobenius generates the complete Galois group of the
--   constant extension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L229-L236
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L229-L236

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.zpowers_constantFrobenius_eq_top
    (P : BasePrime) (r : Rank) :
    Subgroup.zpowers (constantFrobenius P r) = ⊤ := by sorry
