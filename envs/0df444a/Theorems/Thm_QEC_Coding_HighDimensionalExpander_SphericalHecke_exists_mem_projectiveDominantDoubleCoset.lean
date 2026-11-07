-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_exists_mem_projectiveDominantDoubleCoset
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.exists_mem_projectiveDominantDoubleCoset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:43:12.228657+00:00
-- url     : https://prove2.me/theorems/80d98626-1d3f-4ac3-98b5-544d90514581
-- title:
--   Spherical Hecke: exists mem projective Dominant Double Coset
-- statement:
--   Every positive-rank projective local element lies in a double coset
--   indexed by a scalar-normalized dominant type.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2343-L2352
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2343-L2352

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.exists_mem_projectiveDominantDoubleCoset
    (k : Type u) [Field k] {n : ℕ}
    (g : PGL(Fin (n + 1), LocalFunctionField k)) :
    ∃ weight : ProjectiveDominantCoweight n,
      g ∈ projectiveDominantDoubleCoset k weight := by sorry
