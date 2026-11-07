-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_clearedMatrix_det_ne_zero
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.clearedMatrix_det_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:03:49.901213+00:00
-- url     : https://prove2.me/theorems/284d1ca2-9b7f-410d-80b7-a94caa086a6f
-- title:
--   Spherical Hecke: cleared Matrix det ne zero
-- statement:
--   Clearing denominators in an invertible matrix does not destroy its
--   nonzero determinant over the valuation ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L139-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L139-L154

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.clearedMatrix_det_ne_zero
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    (clearedMatrix (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).det ≠ 0 := by sorry
