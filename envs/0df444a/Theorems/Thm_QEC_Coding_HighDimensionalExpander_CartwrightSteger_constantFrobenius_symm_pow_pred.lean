-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_symm_pow_pred
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_symm_pow_pred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:47:59.71696+00:00
-- url     : https://prove2.me/theorems/50d39f73-c298-41a8-afb9-3f087168ec7c
-- title:
--   Cartwright Steger: constant Frobenius symm pow pred
-- statement:
--   The Cartwright Steger construction uses the constant Frobenius symm pow pred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L324-L336
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L324-L336

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_symm_pow_pred (P : BasePrime) (r : Rank) :
    (constantFrobenius P r).symm ^ (r.matrixRank - 1) =
      constantFrobenius P r := by sorry
