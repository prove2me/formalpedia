-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_iUnion_dominantDoubleCoset
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.iUnion_dominantDoubleCoset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:06:32.619515+00:00
-- url     : https://prove2.me/theorems/a3681276-91e6-49ec-9549-33df49882afd
-- title:
--   Spherical Hecke: i Union dominant Double Coset
-- statement:
--   The dominant Cartan double cosets form a countable compact cover.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2333-L2339
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2333-L2339

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.iUnion_dominantDoubleCoset
    (k : Type u) [Field k] {d : ℕ} :
    ⋃ weight : DominantCoweight d, dominantDoubleCoset k weight = Set.univ := by sorry
