-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_permutationUnitary_eq_of_agree_on_support
-- name    : SoficGroups.KunRootedIndicatorCrossing.permutationUnitary_eq_of_agree_on_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/02ea9471-5de7-4592-b2d1-445d60c375b3
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.permutationUnitary_eq_of_agree_on_support
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

theorem SoficGroups.KunRootedIndicatorCrossing.permutationUnitary_eq_of_agree_on_support
    {V : Type*} [Fintype V] (p q : Equiv.Perm V)
    (ξ : EuclideanSpace ℂ V)
    (h : ∀ x : V, ξ x ≠ 0 → p x = q x) :
    permutationUnitary p ξ = permutationUnitary q ξ := by sorry
