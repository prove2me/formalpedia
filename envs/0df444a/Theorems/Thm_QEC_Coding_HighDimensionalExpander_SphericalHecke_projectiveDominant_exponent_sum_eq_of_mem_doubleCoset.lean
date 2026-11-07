-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_exponent_sum_eq_of_mem_doubleCoset
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_exponent_sum_eq_of_mem_doubleCoset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:48:58.876852+00:00
-- url     : https://prove2.me/theorems/d0a98723-2d05-401c-963f-00b07094f92d
-- title:
--   Spherical Hecke: projective Dominant exponent sum eq of mem double Coset
-- statement:
--   The determinant recovers the sum of the normalized Cartan exponents;
--   integral left/right factors and the projective scalar all have order zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2738-L2752
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2738-L2752

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_exponent_sum_eq_of_mem_doubleCoset
    (k : Type u) [Field k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n)
    (hmem : dominantCoweight k a.toDominant ∈
      projectiveDominantDoubleCoset k b) :
    (∑ i, (a.toDominant.exponent i : ℤ)) =
      ∑ i, (b.toDominant.exponent i : ℤ) := by sorry
