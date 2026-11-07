-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_left_mul_mem_dominantDoubleCoset
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.left_mul_mem_dominantDoubleCoset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:42:34.019943+00:00
-- url     : https://prove2.me/theorems/f554a717-7e55-4de1-a7b7-9f2b6cb4bb2b
-- title:
--   Spherical Hecke: left mul mem dominant Double Coset
-- statement:
--   The Spherical Hecke construction uses the left mul mem dominant Double Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2400-L2412
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2400-L2412

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.left_mul_mem_dominantDoubleCoset
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d)
    {h x : PGL(Fin d, LocalFunctionField k)}
    (hh : h ∈ maximalCompact k d)
    (hx : x ∈ dominantDoubleCoset k weight) :
    h * x ∈ dominantDoubleCoset k weight := by sorry
