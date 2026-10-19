-- Prove2me | Theorems.Thm_SoficGroups_KunRealComplexMarkovBridge_norm_iterate_permutationMarkov_indicator_sub_iterate_sq
-- name    : SoficGroups.KunRealComplexMarkovBridge.norm_iterate_permutationMarkov_indicator_sub_iterate_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/356c2c95-e620-4be1-b0b9-8628f7fe3567
-- title:
--   SoficGroups.KunRealComplexMarkovBridge.norm_iterate_permutationMarkov_indicator_sub_iterate_sq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRealComplexMarkovBridge
open scoped BigOperators ComplexOrder InnerProductSpace Topology

theorem SoficGroups.KunRealComplexMarkovBridge.norm_iterate_permutationMarkov_indicator_sub_iterate_sq
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) (k : ℕ) :
    ‖((permutationMarkov p)^[k + 1]) (indicatorVector f) -
        ((permutationMarkov p)^[k]) (indicatorVector f)‖ ^ 2 =
      ∑ x, ((((realMarkov p)^[k + 1]) f) x -
        (((realMarkov p)^[k]) f) x) ^ 2 := by sorry
