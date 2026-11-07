-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_toLin_constantRegularMatrix
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.toLin_constantRegularMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:52:58.231687+00:00
-- url     : https://prove2.me/theorems/3433cc14-5a01-467a-a791-ac2dac5d6dd4
-- title:
--   Cartwright Steger: to Lin constant Regular Matrix
-- statement:
--   The regular matrix of a constant is the matrix of multiplication by that
--   constant in the fixed constant-field basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L165-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L165-L172

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.toLin_constantRegularMatrix
    (P : BasePrime) (r : Rank) (a : ConstantExtension P r) :
    Matrix.toLin (constantBasis P r) (constantBasis P r)
        (constantRegularMatrix P r a) =
      constantMultiplicationLinearMap P r a := by sorry
