-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_orderTop_finset_sum_lowerBound
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.orderTop_finset_sum_lowerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:46:24.811196+00:00
-- url     : https://prove2.me/theorems/d8e0d70e-037e-4edb-90e7-64b883e14de8
-- title:
--   Spherical Hecke: order Top finset sum lower Bound
-- statement:
--   The Spherical Hecke construction uses the order Top finset sum lower Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1560-L1572
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1560-L1572

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.orderTop_finset_sum_lowerBound
    {k : Type u} [Field k]
    {α : Type*} {s : Finset α} {f : α → LocalFunctionField k}
    {m : WithTop ℤ} (h : ∀ a ∈ s, m ≤ (f a).orderTop) :
    m ≤ (∑ a ∈ s, f a).orderTop := by sorry
