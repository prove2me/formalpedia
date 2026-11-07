-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_range_toLin_mul_generalLinear
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.range_toLin_mul_generalLinear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:52:56.545688+00:00
-- url     : https://prove2.me/theorems/eeb17154-6609-4544-ba89-ea4abb50fe33
-- title:
--   Cartwright Steger: range to Lin mul general Linear
-- statement:
--   Right multiplication by an invertible residue matrix does not change a
--   matrix's image subspace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L228-L249
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L228-L249

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.range_toLin_mul_generalLinear
    (P : BasePrime) (r : Rank)
    (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P))
    (C : Matrix.GeneralLinearGroup
      (Fin r.matrixRank) (BaseField P)) :
    LinearMap.range
        (Matrix.toLin (constantBasis P r) (constantBasis P r)
          (A * (C : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BaseField P)))) =
      LinearMap.range
        (Matrix.toLin (constantBasis P r) (constantBasis P r) A) := by sorry
