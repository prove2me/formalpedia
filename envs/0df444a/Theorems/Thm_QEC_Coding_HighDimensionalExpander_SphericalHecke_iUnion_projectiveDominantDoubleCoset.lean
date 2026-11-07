-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_iUnion_projectiveDominantDoubleCoset
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.iUnion_projectiveDominantDoubleCoset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:48:41.548904+00:00
-- url     : https://prove2.me/theorems/503d5ef7-a247-44f1-9560-f42e784ae277
-- title:
--   Spherical Hecke: i Union projective Dominant Double Coset
-- statement:
--   The normalized projective Cartan double cosets give the required
--   countable compact cover in every positive rank, in particular ranks three
--   and four.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2357-L2365
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2357-L2365

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.iUnion_projectiveDominantDoubleCoset
    (k : Type u) [Field k] {n : ℕ} :
    ⋃ weight : ProjectiveDominantCoweight n,
      projectiveDominantDoubleCoset k weight = Set.univ := by sorry
