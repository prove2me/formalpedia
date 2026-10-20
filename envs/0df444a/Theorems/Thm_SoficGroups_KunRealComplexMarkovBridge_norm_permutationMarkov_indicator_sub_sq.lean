-- Prove2me | Theorems.Thm_SoficGroups_KunRealComplexMarkovBridge_norm_permutationMarkov_indicator_sub_sq
-- name    : SoficGroups.KunRealComplexMarkovBridge.norm_permutationMarkov_indicator_sub_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/870e0484-0574-4df6-8148-50680c6ea23f
-- title:
--   SoficGroups.KunRealComplexMarkovBridge.norm_permutationMarkov_indicator_sub_sq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRealComplexMarkovBridge
open scoped BigOperators ComplexOrder InnerProductSpace Topology

theorem SoficGroups.KunRealComplexMarkovBridge.norm_permutationMarkov_indicator_sub_sq
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) :
    ‖permutationMarkov p (indicatorVector f) - indicatorVector f‖ ^ 2 =
      ∑ x, (realMarkov p f x - f x) ^ 2 := by sorry
