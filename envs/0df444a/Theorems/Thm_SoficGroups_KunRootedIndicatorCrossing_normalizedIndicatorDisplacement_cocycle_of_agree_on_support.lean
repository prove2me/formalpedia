-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_normalizedIndicatorDisplacement_cocycle_of_agree_on_support
-- name    : SoficGroups.KunRootedIndicatorCrossing.normalizedIndicatorDisplacement_cocycle_of_agree_on_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/3e2c952d-905c-4eb3-91ae-1d77b4e48ea9
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.normalizedIndicatorDisplacement_cocycle_of_agree_on_support
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

theorem SoficGroups.KunRootedIndicatorCrossing.normalizedIndicatorDisplacement_cocycle_of_agree_on_support
    {G ι V : Type*} [Group G] [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (a g : G)
    (hroot : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * g) x = (σ a * σ g) x) :
    normalizedIndicatorDisplacement p f (σ (a * g)) =
      normalizedIndicatorDisplacement p f (σ a) +
        permutationUnitary (σ a)
          (normalizedIndicatorDisplacement p f (σ g)) := by sorry
