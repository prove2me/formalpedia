-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_permutationUnitary_model_mul_of_agree_on_support
-- name    : SoficGroups.KunRootedIndicatorCrossing.permutationUnitary_model_mul_of_agree_on_support
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/237c0b9d-5260-402d-aa09-55a0f17c6d05
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.permutationUnitary_model_mul_of_agree_on_support
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

theorem SoficGroups.KunRootedIndicatorCrossing.permutationUnitary_model_mul_of_agree_on_support
    {G V : Type*} [Group G] [Fintype V]
    (σ : G → Equiv.Perm V) (a g : G) (ξ : EuclideanSpace ℂ V)
    (hroot : ∀ x : V, ξ x ≠ 0 →
      σ (a * g) x = (σ a * σ g) x) :
    permutationUnitary (σ (a * g)) ξ =
      permutationUnitary (σ a) (permutationUnitary (σ g) ξ) := by sorry
