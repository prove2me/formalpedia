-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveTranspose_mem_dominantDoubleCoset
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveTranspose_mem_dominantDoubleCoset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:43:15.698403+00:00
-- url     : https://prove2.me/theorems/743d4abd-7124-4ab7-91ac-9a49ca8d5ab8
-- title:
--   Spherical Hecke: projective Transpose mem dominant Double Coset
-- statement:
--   Matrix transpose preserves every dominant Cartan double coset.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2460-L2479
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2460-L2479

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveTranspose_mem_dominantDoubleCoset
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d)
    {x : PGL(Fin d, LocalFunctionField k)}
    (hx : x ∈ dominantDoubleCoset k weight) :
    projectiveTranspose x ∈ dominantDoubleCoset k weight := by sorry
