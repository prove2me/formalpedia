-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_toMatrix_normalBasis_three
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_toMatrix_normalBasis_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:53:00.163592+00:00
-- url     : https://prove2.me/theorems/757fac1a-029a-4cee-8184-d9addc3ffebf
-- title:
--   Cartwright Steger: constant Frobenius to Matrix normal Basis three
-- statement:
--   Frobenius in the rank-three consecutive normal basis is the explicit
--   three-cycle matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L349-L365
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L349-L365

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_toMatrix_normalBasis_three (P : BasePrime) :
    LinearMap.toMatrix (frobeniusNormalBasis P .three)
        (frobeniusNormalBasis P .three)
        (constantFrobenius P .three).toLinearEquiv.toLinearMap =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] := by sorry
