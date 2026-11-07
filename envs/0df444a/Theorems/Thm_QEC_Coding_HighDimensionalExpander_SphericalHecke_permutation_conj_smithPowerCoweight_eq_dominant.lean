-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_permutation_conj_smithPowerCoweight_eq_dominant
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.permutation_conj_smithPowerCoweight_eq_dominant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:48:35.334988+00:00
-- url     : https://prove2.me/theorems/69996629-1511-4da7-a145-6a2e2a23cbb8
-- title:
--   Spherical Hecke: permutation conj smith Power Coweight eq dominant
-- statement:
--   The Spherical Hecke construction uses the permutation conj smith Power Coweight eq dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2266-L2279
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2266-L2279

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.permutation_conj_smithPowerCoweight_eq_dominant
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    permutationCoweight k
          (dominantSortPermutation
            (smithExponent (k := k) (d := d) A)) *
        smithPowerCoweight (k := k) (d := d) A *
        (permutationCoweight k
          (dominantSortPermutation
            (smithExponent (k := k) (d := d) A)))⁻¹ =
      dominantCoweight k (smithDominantCoweight A) := by sorry
