-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_first_exponent_eq_of_doubleCoset_inter_nonempty
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_first_exponent_eq_of_doubleCoset_inter_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:43:24.977977+00:00
-- url     : https://prove2.me/theorems/4548abd1-59a6-4583-b7ef-f658388df986
-- title:
--   Spherical Hecke: projective Dominant first exponent eq of double Coset inter nonempty
-- statement:
--   The Spherical Hecke construction uses the projective Dominant first exponent eq of double Coset inter nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2715-L2734
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2715-L2734

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_first_exponent_eq_of_doubleCoset_inter_nonempty
    (k : Type u) [Field k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n)
    (hinter : (projectiveDominantDoubleCoset k a ∩
      projectiveDominantDoubleCoset k b).Nonempty) :
    a.toDominant.exponent (0 : Fin (n + 1)) =
      b.toDominant.exponent (0 : Fin (n + 1)) := by sorry
