-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_range_toLin_constant_conjugate_one_sub_frobeniusGL_inv
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.range_toLin_constant_conjugate_one_sub_frobeniusGL_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:52:55.99766+00:00
-- url     : https://prove2.me/theorems/bd3b709f-aec5-4af5-8b36-2d696577c248
-- title:
--   Cartwright Steger: range to Lin constant conjugate one sub frobenius GL inv
-- statement:
--   Constant conjugation transports the image of `1 - Frobenius⁻¹` to
--   the corresponding multiplicative translate of the Frobenius-difference
--   hyperplane.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L189-L224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L189-L224

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.range_toLin_constant_conjugate_one_sub_frobeniusGL_inv
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    LinearMap.range
        (Matrix.toLin (constantBasis P r) (constantBasis P r)
          (constantRegularMatrix P r (u : ConstantExtension P r) *
            (1 - ((frobeniusGL P r)⁻¹ :
              Matrix.GeneralLinearGroup
                (Fin r.matrixRank) (BaseField P))) *
            constantRegularMatrix P r
              ((u : ConstantExtension P r)⁻¹))) =
      (frobeniusDifferenceRange P r).map
        (constantMultiplicationLinearMap P r u) := by sorry
