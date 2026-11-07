-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantDoubleCoset_fundamental
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantDoubleCoset_fundamental
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:48:18.139334+00:00
-- url     : https://prove2.me/theorems/4914fe0a-9672-45d2-8b05-de94c3befa8f
-- title:
--   Spherical Hecke: dominant Double Coset fundamental
-- statement:
--   The Spherical Hecke construction uses the dominant Double Coset fundamental property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2207-L2212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2207-L2212

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantDoubleCoset_fundamental
    (k : Type u) [Field k] (d r : ℕ) :
    dominantDoubleCoset k (fundamentalDominantCoweight d r) =
      fundamentalDoubleCoset k d r := by sorry
