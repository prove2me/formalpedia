-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_normalizedPairDisplacement_inner_diagonal
-- name    : SoficGroups.KunRootedIndicatorCrossing.normalizedPairDisplacement_inner_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/df09d386-8b6d-403b-9f22-f36be17a01e0
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.normalizedPairDisplacement_inner_diagonal
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

theorem SoficGroups.KunRootedIndicatorCrossing.normalizedPairDisplacement_inner_diagonal
    {G ι V : Type*} [Group G] [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (a g h j k : G)
    (hg : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * g) x = (σ a * σ g) x)
    (hh : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * h) x = (σ a * σ h) x)
    (hj : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * j) x = (σ a * σ j) x)
    (hk : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * k) x = (σ a * σ k) x) :
    @inner ℂ (EuclideanSpace ℂ V) _
      (normalizedPairDisplacement p f σ (a * g, a * h))
      (normalizedPairDisplacement p f σ (a * j, a * k)) =
    @inner ℂ (EuclideanSpace ℂ V) _
      (normalizedPairDisplacement p f σ (g, h))
      (normalizedPairDisplacement p f σ (j, k)) := by sorry
