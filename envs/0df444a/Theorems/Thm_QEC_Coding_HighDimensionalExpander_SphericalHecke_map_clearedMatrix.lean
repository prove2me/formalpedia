-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_map_clearedMatrix
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.map_clearedMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:44:54.589572+00:00
-- url     : https://prove2.me/theorems/727cfcc5-e43a-4e0d-8207-ebc75218ad4e
-- title:
--   Spherical Hecke: map cleared Matrix
-- statement:
--   Base-changing the cleared matrix back to the local field recovers the
--   uniformizer scalar multiple of the original matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L128-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L128-L135

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.map_clearedMatrix
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) :
    (SubringClass.subtype (Valued.integer (LocalFunctionField k))).mapMatrix
        (clearedMatrix A) =
      (uniformizerUnit k : LocalFunctionField k) ^ matrixClearingExponent A • A := by sorry
