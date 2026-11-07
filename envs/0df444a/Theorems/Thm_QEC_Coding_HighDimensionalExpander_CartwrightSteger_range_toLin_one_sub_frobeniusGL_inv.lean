-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_range_toLin_one_sub_frobeniusGL_inv
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.range_toLin_one_sub_frobeniusGL_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:29:50.265647+00:00
-- url     : https://prove2.me/theorems/b3a29a23-b082-4e48-af4e-f24390763176
-- title:
--   Cartwright Steger: range to Lin one sub frobenius GL inv
-- statement:
--   The matrix `1 - Frobenius⁻¹` has precisely the Frobenius-difference
--   hyperplane as its image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L176-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L176-L184

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.range_toLin_one_sub_frobeniusGL_inv
    (P : BasePrime) (r : Rank) :
    LinearMap.range
        (Matrix.toLin (constantBasis P r) (constantBasis P r)
          (1 - ((frobeniusGL P r)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank) (BaseField P)))) =
      frobeniusDifferenceRange P r := by sorry
