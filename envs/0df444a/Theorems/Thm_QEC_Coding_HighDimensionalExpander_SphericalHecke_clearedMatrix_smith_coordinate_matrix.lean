-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_clearedMatrix_smith_coordinate_matrix
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.clearedMatrix_smith_coordinate_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:44:59.270075+00:00
-- url     : https://prove2.me/theorems/cb65feb4-2dce-43aa-a8aa-c7f2a8554e07
-- title:
--   Spherical Hecke: cleared Matrix smith coordinate matrix
-- statement:
--   In the two constructed Smith bases, the cleared matrix is diagonal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L361-L379
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L361-L379

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.clearedMatrix_smith_coordinate_matrix
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    LinearMap.toMatrix
        (smithDomainBasis (k := k) (d := d) A)
        (smithAmbientBasis (k := k) (d := d) A)
        (clearedPowerSeriesMatrix (k := k) (d := d)
          (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).mulVecLin =
      Matrix.diagonal (smithDiagonalCoeff (k := k) (d := d) A) := by sorry
