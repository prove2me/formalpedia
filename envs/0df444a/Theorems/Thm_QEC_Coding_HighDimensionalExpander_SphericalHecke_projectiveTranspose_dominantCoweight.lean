-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveTranspose_dominantCoweight
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveTranspose_dominantCoweight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:47:00.158855+00:00
-- url     : https://prove2.me/theorems/edffd842-d628-4afb-b7b0-35205b42548c
-- title:
--   Spherical Hecke: projective Transpose dominant Coweight
-- statement:
--   Projective transpose fixes every dominant diagonal representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1903-L1920
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1903-L1920

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveTranspose_dominantCoweight
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d) :
    projectiveTranspose (dominantCoweight k weight) =
      dominantCoweight k weight := by sorry
