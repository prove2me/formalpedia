-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_permutation_indicator_markov_defect_norm_sq
-- name    : SoficGroups.KunRootedIndicatorCrossing.permutation_indicator_markov_defect_norm_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/62fa432e-4d93-496a-bca0-abef220eece7
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.permutation_indicator_markov_defect_norm_sq
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

theorem SoficGroups.KunRootedIndicatorCrossing.permutation_indicator_markov_defect_norm_sq
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) :
    ‖permutationMarkov p (indicatorVector f) - indicatorVector f‖ ^ 2 =
      ∑ x, ((∑ i, f ((p i).symm x)) /
        (Fintype.card ι : ℝ) - f x) ^ 2 := by sorry
