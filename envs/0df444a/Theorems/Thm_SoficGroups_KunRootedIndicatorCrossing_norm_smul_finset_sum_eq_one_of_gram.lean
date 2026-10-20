-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_norm_smul_finset_sum_eq_one_of_gram
-- name    : SoficGroups.KunRootedIndicatorCrossing.norm_smul_finset_sum_eq_one_of_gram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/95f8a6fc-4006-4d20-b4c2-12ced970a215
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.norm_smul_finset_sum_eq_one_of_gram
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

theorem SoficGroups.KunRootedIndicatorCrossing.norm_smul_finset_sum_eq_one_of_gram
    {N I H : Type*} {E : N → Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [∀ n, NormedAddCommGroup (E n)]
    [∀ n, InnerProductSpace ℂ (E n)]
    (l : Filter N) [NeBot l]
    (z : ∀ n, I → E n) (v : I → H)
    (hgram : ∀ i j,
      Tendsto (fun n => ⟪z n i, z n j⟫_ℂ) l
        (𝓝 ⟪v i, v j⟫_ℂ))
    (F : Finset I) (c : ℂ)
    (hnorm : ∀ n, ‖c • ∑ i ∈ F, z n i‖ = 1) :
    ‖c • ∑ i ∈ F, v i‖ = 1 := by sorry
