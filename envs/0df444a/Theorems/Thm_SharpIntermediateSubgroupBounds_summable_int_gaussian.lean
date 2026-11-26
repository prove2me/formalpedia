-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_summable_int_gaussian
-- name    : SharpIntermediateSubgroupBounds.summable_int_gaussian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:41:05.30867+00:00
-- url     : https://prove2.me/theorems/fa17ec54-0760-534c-a1ff-1be5f58134c7
-- title:
--   Sharp Intermediate Subgroup Bounds: summable int gaussian
-- statement:
--   Summability of an arbitrary positive Gaussian on `ℤ`.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Theta.lean#L165-L173
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Theta.lean#L165-L173

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.summable_int_gaussian {A : ℝ} (hA : 0 < A) :
    Summable (fun z : ℤ ↦ Real.exp (-A * (z : ℝ) ^ 2)) := by sorry
