-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_inner_smul_fintype_sum
-- name    : SoficGroups.KunRootedWordPower.inner_smul_fintype_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/896e67dd-c536-4c7e-978e-49973ec0271d
-- title:
--   SoficGroups.KunRootedWordPower.inner_smul_fintype_sum
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v w

theorem SoficGroups.KunRootedWordPower.inner_smul_fintype_sum
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : ι → E) (c : ℂ) :
    ⟪c • ∑ i, x i, c • ∑ j, y j⟫_ℂ =
      star c * (∑ i, ∑ j, ⟪x i, y j⟫_ℂ) * c := by sorry
