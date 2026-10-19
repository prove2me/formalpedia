-- Prove2me | Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_norm_finset_sum_le_pair_add
-- name    : SoficGroups.KunThomInvariantOrthogonal.norm_finset_sum_le_pair_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/812d00dd-53c8-4e6f-b360-1578ab3921dc
-- title:
--   SoficGroups.KunThomInvariantOrthogonal.norm_finset_sum_le_pair_add
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomInvariantOrthogonal
open Filter Topology
open scoped ComplexConjugate Pointwise
universe u v
variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
omit [InnerProductSpace ℂ H]

theorem SoficGroups.KunThomInvariantOrthogonal.norm_finset_sum_le_pair_add
    {X : Type*} (S : Finset X) (f : X → H)
    (a b : X) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (r : ℝ) (hnorm : ∀ s ∈ S, ‖f s‖ = r) :
    ‖∑ s ∈ S, f s‖ ≤
      ‖f a + f b‖ + ((S.card : ℝ) - 2) * r := by sorry
