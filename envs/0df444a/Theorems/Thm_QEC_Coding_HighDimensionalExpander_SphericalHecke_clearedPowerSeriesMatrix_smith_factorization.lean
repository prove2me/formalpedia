-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_clearedPowerSeriesMatrix_smith_factorization
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.clearedPowerSeriesMatrix_smith_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:45:01.850753+00:00
-- url     : https://prove2.me/theorems/eb9c540c-4153-4757-ac5b-7fee38b5a1d0
-- title:
--   Spherical Hecke: cleared Power Series Matrix smith factorization
-- statement:
--   Matrix-level Smith factorization with both change-of-basis matrices
--   certified as elements of `GL_d(k[[X]])`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L405-L439
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L405-L439

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.clearedPowerSeriesMatrix_smith_factorization
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    clearedPowerSeriesMatrix (k := k) (d := d)
        (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) =
      (smithAmbientGeneralLinear (k := k) (d := d) A :
          Matrix (Fin d) (Fin d) (IntegerRing k)) *
        Matrix.diagonal (smithDiagonalCoeff (k := k) (d := d) A) *
      (((smithDomainGeneralLinear (k := k) (d := d) A)⁻¹ :
          GL (Fin d) (IntegerRing k)) :
            Matrix (Fin d) (Fin d) (IntegerRing k)) := by sorry
