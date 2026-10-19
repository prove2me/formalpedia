-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_permutation_indicator_displacement_norm_sq
-- name    : SoficGroups.KunRootedIndicatorCrossing.permutation_indicator_displacement_norm_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/35092e91-0734-464e-90e2-b0ded148369e
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.permutation_indicator_displacement_norm_sq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology

theorem SoficGroups.KunRootedIndicatorCrossing.permutation_indicator_displacement_norm_sq
    {V : Type*} [Fintype V] (p : Equiv.Perm V) (f : V → ℝ) :
    ‖permutationUnitary p (indicatorVector f) - indicatorVector f‖ ^ 2 =
      ∑ x, (f (p.symm x) - f x) ^ 2 := by sorry
