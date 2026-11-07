-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_permutation_conj_smithPower_eq_dominant
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.permutation_conj_smithPower_eq_dominant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:48:36.962596+00:00
-- url     : https://prove2.me/theorems/a0f089ac-79db-410f-ab70-bd04d7ec5e7f
-- title:
--   Spherical Hecke: permutation conj smith Power eq dominant
-- statement:
--   Sorting the Smith exponents is implemented by conjugation with an actual
--   permutation matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2239-L2264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2239-L2264

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.permutation_conj_smithPower_eq_dominant
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    permutationGeneralLinear (LocalFunctionField k)
          (dominantSortPermutation
            (smithExponent (k := k) (d := d) A)) *
        smithPowerGeneralLinearLocal (k := k) (d := d) A *
        (permutationGeneralLinear (LocalFunctionField k)
          (dominantSortPermutation
            (smithExponent (k := k) (d := d) A)))⁻¹ =
      dominantGeneralLinear k (smithDominantCoweight A) := by sorry
