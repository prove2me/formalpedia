-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_subgroup_doubleCoset_inv_eq_of_inv_eq_conj
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.subgroup_doubleCoset_inv_eq_of_inv_eq_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:41:10.614763+00:00
-- url     : https://prove2.me/theorems/6900751b-d8b7-4ca7-bd03-32e3fb52499b
-- title:
--   Spherical Hecke: subgroup double Coset inv eq of inv eq conj
-- statement:
--   Inverting a subgroup double coset replaces its representative by its
--   inverse; a conjugating subgroup element is absorbed on the two sides.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3391-L3405
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3391-L3405

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.subgroup_doubleCoset_inv_eq_of_inv_eq_conj
    {G : Type*} [Group G] (K : Subgroup G) {a b p : G}
    (hp : p ∈ K) (hab : a⁻¹ = p * b * p⁻¹) :
    ((K : Set G) * {a} * (K : Set G))⁻¹ =
      (K : Set G) * {b} * (K : Set G) := by sorry
