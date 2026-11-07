-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_right_mul_mem_dominantDoubleCoset_iff
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.right_mul_mem_dominantDoubleCoset_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:48:52.019184+00:00
-- url     : https://prove2.me/theorems/a3c99bbb-d1e9-4300-9841-65588895ea8b
-- title:
--   Spherical Hecke: right mul mem dominant Double Coset iff
-- statement:
--   The Spherical Hecke construction uses the right mul mem dominant Double Coset iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2438-L2449
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2438-L2449

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.right_mul_mem_dominantDoubleCoset_iff
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d)
    {h x : PGL(Fin d, LocalFunctionField k)}
    (hh : h ∈ maximalCompact k d) :
    x * h ∈ dominantDoubleCoset k weight ↔
      x ∈ dominantDoubleCoset k weight := by sorry
