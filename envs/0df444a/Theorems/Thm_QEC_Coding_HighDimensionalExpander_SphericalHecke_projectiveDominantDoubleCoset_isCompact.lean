-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominantDoubleCoset_isCompact
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominantDoubleCoset_isCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:43:14.448753+00:00
-- url     : https://prove2.me/theorems/c27ce3d5-b8b9-4a6f-9891-65c5b4b93dfc
-- title:
--   Spherical Hecke: projective Dominant Double Coset is Compact
-- statement:
--   The Spherical Hecke construction uses the projective Dominant Double Coset is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2367-L2371
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2367-L2371

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominantDoubleCoset_isCompact
    (k : Type u) [Field k] [Finite k] {n : ℕ}
    (weight : ProjectiveDominantCoweight n) :
    IsCompact (projectiveDominantDoubleCoset k weight) := by sorry
