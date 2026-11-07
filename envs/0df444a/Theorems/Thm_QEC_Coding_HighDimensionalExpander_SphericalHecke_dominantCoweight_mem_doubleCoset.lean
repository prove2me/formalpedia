-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantCoweight_mem_doubleCoset
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantCoweight_mem_doubleCoset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:43:05.88074+00:00
-- url     : https://prove2.me/theorems/180b93f2-bac9-41b0-9612-b288027aced6
-- title:
--   Spherical Hecke: dominant Coweight mem double Coset
-- statement:
--   The Spherical Hecke construction uses the dominant Coweight mem double Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2100-L2108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2100-L2108

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantCoweight_mem_doubleCoset
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d) :
    dominantCoweight k weight ∈ dominantDoubleCoset k weight := by sorry
