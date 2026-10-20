-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_permutation_indicator_displacement_norm_le_card_mul_markov_defect
-- name    : SoficGroups.KunRootedIndicatorCrossing.permutation_indicator_displacement_norm_le_card_mul_markov_defect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/35da24aa-2f7c-46e1-b498-0ee0b255c95c
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.permutation_indicator_displacement_norm_le_card_mul_markov_defect
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

theorem SoficGroups.KunRootedIndicatorCrossing.permutation_indicator_displacement_norm_le_card_mul_markov_defect
    {ι V : Type*} [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (i : ι) :
    ‖permutationUnitary (p i) (indicatorVector f) - indicatorVector f‖ ≤
      (Fintype.card ι : ℝ) *
        ‖permutationMarkov p (indicatorVector f) - indicatorVector f‖ := by sorry
