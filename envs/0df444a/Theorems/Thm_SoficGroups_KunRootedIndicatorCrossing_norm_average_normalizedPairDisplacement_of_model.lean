-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_norm_average_normalizedPairDisplacement_of_model
-- name    : SoficGroups.KunRootedIndicatorCrossing.norm_average_normalizedPairDisplacement_of_model
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/ef6e6e99-762d-492f-883a-b66acfaae410
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.norm_average_normalizedPairDisplacement_of_model
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

theorem SoficGroups.KunRootedIndicatorCrossing.norm_average_normalizedPairDisplacement_of_model
    {G ι V : Type*} [Group G] [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (s : ι → G)
    (hone : σ 1 = 1) (hgenerator : ∀ i, σ (s i) = p i)
    (hdefect : permutationMarkov p (indicatorVector f) ≠
      indicatorVector f) :
    ‖(Fintype.card ι : ℂ)⁻¹ •
      ∑ i, normalizedPairDisplacement p f σ (s i, 1)‖ = 1 := by sorry
