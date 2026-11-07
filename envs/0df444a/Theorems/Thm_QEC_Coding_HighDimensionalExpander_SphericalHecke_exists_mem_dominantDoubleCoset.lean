-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_exists_mem_dominantDoubleCoset
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.exists_mem_dominantDoubleCoset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:43:05.758395+00:00
-- url     : https://prove2.me/theorems/c891ecef-d480-4ab0-ae4b-7909cdc80cac
-- title:
--   Spherical Hecke: exists mem dominant Double Coset
-- statement:
--   Every projective local element has a dominant Cartan representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2325-L2330
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2325-L2330

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.exists_mem_dominantDoubleCoset
    (k : Type u) [Field k] {d : ℕ}
    (g : PGL(Fin d, LocalFunctionField k)) :
    ∃ weight : DominantCoweight d, g ∈ dominantDoubleCoset k weight := by sorry
