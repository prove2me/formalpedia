-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_shiftedTheta_eq_iff
-- name    : SharpIntermediateSubgroupBounds.shiftedTheta_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:53:49.866385+00:00
-- url     : https://prove2.me/theorems/5e9aa61f-068d-4c40-aaed-291c6f097038
-- title:
--   Sharp Intermediate Subgroup Bounds: shifted Theta eq iff
-- statement:
--   Equality in the shifted-theta estimate holds exactly at integral shifts.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Theta.lean#L417-L423
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Theta.lean#L417-L423

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

theorem SharpIntermediateSubgroupBounds.shiftedTheta_eq_iff {p x : ℝ} (hp : 1 < p) :
    shiftedTheta p x = gaussianTheta p ↔ ∃ z : ℤ, (z : ℝ) = x := by sorry
