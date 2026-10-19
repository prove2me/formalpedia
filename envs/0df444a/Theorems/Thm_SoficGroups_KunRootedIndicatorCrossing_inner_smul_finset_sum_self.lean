-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_inner_smul_finset_sum_self
-- name    : SoficGroups.KunRootedIndicatorCrossing.inner_smul_finset_sum_self
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/2805ac90-d667-4e33-8330-26674a8aca5e
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.inner_smul_finset_sum_self
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

theorem SoficGroups.KunRootedIndicatorCrossing.inner_smul_finset_sum_self
    {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (z : I → E) (F : Finset I) (c : ℂ) :
    ⟪c • ∑ i ∈ F, z i, c • ∑ i ∈ F, z i⟫_ℂ =
      star c * (∑ i ∈ F, ∑ j ∈ F, ⟪z i, z j⟫_ℂ) * c := by sorry
