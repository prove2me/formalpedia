-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_pow_matrixRank
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_pow_matrixRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:44:45.251224+00:00
-- url     : https://prove2.me/theorems/7a801afb-e909-45e0-86f4-f657680837b2
-- title:
--   Cartwright Steger: constant Frobenius pow matrix Rank
-- statement:
--   The Cartwright Steger construction uses the constant Frobenius pow matrix Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L222-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L222-L225

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_pow_matrixRank (P : BasePrime) (r : Rank) :
    constantFrobenius P r ^ r.matrixRank = 1 := by sorry
