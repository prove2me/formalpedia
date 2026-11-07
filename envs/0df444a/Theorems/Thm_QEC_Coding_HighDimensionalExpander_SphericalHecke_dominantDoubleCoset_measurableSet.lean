-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantDoubleCoset_measurableSet
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantDoubleCoset_measurableSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:05:45.929931+00:00
-- url     : https://prove2.me/theorems/4c7df0cc-d3b6-40db-8693-368326501aa5
-- title:
--   Spherical Hecke: dominant Double Coset measurable Set
-- statement:
--   The Spherical Hecke construction uses the dominant Double Coset measurable Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2121-L2124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2121-L2124

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantDoubleCoset_measurableSet
    (k : Type u) [Field k] [Finite k] {d : ℕ}
    (weight : DominantCoweight d) : MeasurableSet (dominantDoubleCoset k weight) := by sorry
