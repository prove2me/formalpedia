-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_exponent_sum_eq_of_doubleCoset_inter_nonempty
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_exponent_sum_eq_of_doubleCoset_inter_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:43:28.214795+00:00
-- url     : https://prove2.me/theorems/7b30bb8f-15ff-459a-9365-857fc8efb956
-- title:
--   Spherical Hecke: projective Dominant exponent sum eq of double Coset inter nonempty
-- statement:
--   The Spherical Hecke construction uses the projective Dominant exponent sum eq of double Coset inter nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2754-L2764
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2754-L2764

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_exponent_sum_eq_of_doubleCoset_inter_nonempty
    (k : Type u) [Field k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n)
    (hinter : (projectiveDominantDoubleCoset k a ∩
      projectiveDominantDoubleCoset k b).Nonempty) :
    (∑ i, (a.toDominant.exponent i : ℤ)) =
      ∑ i, (b.toDominant.exponent i : ℤ) := by sorry
