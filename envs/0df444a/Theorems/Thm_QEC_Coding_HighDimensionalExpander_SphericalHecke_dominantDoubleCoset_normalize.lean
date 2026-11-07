-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantDoubleCoset_normalize
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantDoubleCoset_normalize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:47:46.232677+00:00
-- url     : https://prove2.me/theorems/e208db15-66a9-4ec0-9aaf-caa839abe92c
-- title:
--   Spherical Hecke: dominant Double Coset normalize
-- statement:
--   The Spherical Hecke construction uses the dominant Double Coset normalize property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2002-L2007
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2002-L2007

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantDoubleCoset_normalize
    (k : Type u) [Field k] {n : ℕ}
    (weight : DominantCoweight (n + 1)) :
    dominantDoubleCoset k (normalizeDominantCoweight weight).toDominant =
      dominantDoubleCoset k weight := by sorry
