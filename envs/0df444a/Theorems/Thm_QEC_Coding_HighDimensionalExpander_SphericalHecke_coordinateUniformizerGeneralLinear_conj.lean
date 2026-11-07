-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coordinateUniformizerGeneralLinear_conj
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.coordinateUniformizerGeneralLinear_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:45:33.291837+00:00
-- url     : https://prove2.me/theorems/c33cdd4e-2b88-43f4-a3cd-8de9b834bae9
-- title:
--   Spherical Hecke: coordinate Uniformizer General Linear conj
-- statement:
--   Any two one-coordinate uniformizers are conjugate by a coordinate
--   transposition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L927-L948
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L927-L948

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.coordinateUniformizerGeneralLinear_conj
    (k : Type u) [Field k] {d : ℕ} (i j : Fin d) :
    permutationGeneralLinear (LocalFunctionField k) (Equiv.swap i j) *
        coordinateUniformizerGeneralLinear k d i *
        permutationGeneralLinear (LocalFunctionField k) (Equiv.swap i j)⁻¹ =
      coordinateUniformizerGeneralLinear k d j := by sorry
