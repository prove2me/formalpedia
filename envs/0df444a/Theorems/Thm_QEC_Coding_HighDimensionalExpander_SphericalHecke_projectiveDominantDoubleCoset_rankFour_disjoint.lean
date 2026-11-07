-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominantDoubleCoset_rankFour_disjoint
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominantDoubleCoset_rankFour_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:08:59.603917+00:00
-- url     : https://prove2.me/theorems/1dc1bb1f-1c0b-451c-bb7c-19d2be86019c
-- title:
--   Spherical Hecke: projective Dominant Double Coset rank Four disjoint
-- statement:
--   The Spherical Hecke construction uses the projective Dominant Double Coset rank Four disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3196-L3204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3196-L3204

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominantDoubleCoset_rankFour_disjoint
    (k : Type u) [Field k]
    {a b : ProjectiveDominantCoweight 3} (hab : a ≠ b) :
    Disjoint (projectiveDominantDoubleCoset k a)
      (projectiveDominantDoubleCoset k b) := by sorry
