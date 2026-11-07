-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_permutationCoweight_mem_maximalCompact
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.permutationCoweight_mem_maximalCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:41:18.581191+00:00
-- url     : https://prove2.me/theorems/700786e3-fa08-4d8e-8a53-c2157a34ad0c
-- title:
--   Spherical Hecke: permutation Coweight mem maximal Compact
-- statement:
--   Every coordinate permutation is represented by an element of the actual
--   maximal compact subgroup.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2229-L2235
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2229-L2235

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.permutationCoweight_mem_maximalCompact
    (k : Type u) [Field k] {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    permutationCoweight k σ ∈ maximalCompact k d := by sorry
