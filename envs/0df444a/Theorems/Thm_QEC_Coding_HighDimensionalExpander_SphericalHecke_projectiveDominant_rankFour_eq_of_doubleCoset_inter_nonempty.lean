-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_rankFour_eq_of_doubleCoset_inter_nonempty
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_rankFour_eq_of_doubleCoset_inter_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:43:12.097537+00:00
-- url     : https://prove2.me/theorems/f05f04eb-6cf9-4b4e-9f05-3a7e10255d13
-- title:
--   Spherical Hecke: projective Dominant rank Four eq of double Coset inter nonempty
-- statement:
--   Full uniqueness of the normalized dominant Cartan type in rank four.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3164-L3194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3164-L3194

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_rankFour_eq_of_doubleCoset_inter_nonempty
    (k : Type u) [Field k]
    (a b : ProjectiveDominantCoweight 3)
    (hinter : (projectiveDominantDoubleCoset k a ∩
      projectiveDominantDoubleCoset k b).Nonempty) :
    a = b := by sorry
