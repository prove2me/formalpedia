-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_permutationGeneralLinear_conj_diagonal
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.permutationGeneralLinear_conj_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:41:10.282029+00:00
-- url     : https://prove2.me/theorems/e1f565e3-b0b2-4237-9a86-500f12b84093
-- title:
--   Spherical Hecke: permutation General Linear conj diagonal
-- statement:
--   Conjugating a diagonal matrix by a permutation matrix permutes its
--   diagonal coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L906-L923
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L906-L923

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.permutationGeneralLinear_conj_diagonal
    (R : Type u) [CommRing R] {d : ℕ} (σ : Equiv.Perm (Fin d))
    (v : Fin d → Units R) :
    permutationGeneralLinear R σ * diagonalGeneralLinear R d v *
        (permutationGeneralLinear R σ)⁻¹ =
      diagonalGeneralLinear R d (v ∘ σ) := by sorry
