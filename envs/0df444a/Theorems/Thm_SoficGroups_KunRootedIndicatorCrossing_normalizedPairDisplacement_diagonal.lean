-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_normalizedPairDisplacement_diagonal
-- name    : SoficGroups.KunRootedIndicatorCrossing.normalizedPairDisplacement_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/249994c8-ab63-4782-8790-95dfefb4a327
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.normalizedPairDisplacement_diagonal
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

theorem SoficGroups.KunRootedIndicatorCrossing.normalizedPairDisplacement_diagonal
    {G ι V : Type*} [Group G] [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (a g h : G)
    (hg : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * g) x = (σ a * σ g) x)
    (hh : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * h) x = (σ a * σ h) x) :
    normalizedPairDisplacement p f σ (a * g, a * h) =
      permutationUnitary (σ a)
        (normalizedPairDisplacement p f σ (g, h)) := by sorry
