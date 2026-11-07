-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_subgroup_doubleCoset_conj
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.subgroup_doubleCoset_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:49:55.283002+00:00
-- url     : https://prove2.me/theorems/fe4d9556-a924-466b-8ade-4860b023c9bb
-- title:
--   Spherical Hecke: subgroup double Coset conj
-- statement:
--   Conjugating the middle representative by an element of a subgroup does
--   not change its double coset.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3365-L3387
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3365-L3387

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.subgroup_doubleCoset_conj
    {G : Type*} [Group G] (K : Subgroup G) {b p : G} (hp : p ∈ K) :
    (K : Set G) * {p * b * p⁻¹} * (K : Set G) =
      (K : Set G) * {b} * (K : Set G) := by sorry
