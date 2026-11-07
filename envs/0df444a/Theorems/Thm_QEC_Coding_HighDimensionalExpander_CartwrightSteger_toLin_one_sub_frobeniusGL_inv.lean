-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_toLin_one_sub_frobeniusGL_inv
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.toLin_one_sub_frobeniusGL_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:18.235212+00:00
-- url     : https://prove2.me/theorems/b775c408-30d7-44ea-8c38-73fcd9db7dfe
-- title:
--   Cartwright Steger: to Lin one sub frobenius GL inv
-- statement:
--   In the fixed constant-field basis, `1 - Frobenius⁻¹` is exactly the
--   Frobenius-difference linear map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L126-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L126-L161

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.toLin_one_sub_frobeniusGL_inv
    (P : BasePrime) (r : Rank) :
    Matrix.toLin (constantBasis P r) (constantBasis P r)
        (1 - ((frobeniusGL P r)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank) (BaseField P))) =
      frobeniusDifferenceLinearMap P r := by sorry
