-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_exists_hyperfilter_gram_limit_of_pointwise_bound
-- name    : SoficGroups.KunRootedIndicatorCrossing.exists_hyperfilter_gram_limit_of_pointwise_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/d0b25197-2d9a-425d-b8a7-43639076007a
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.exists_hyperfilter_gram_limit_of_pointwise_bound
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

theorem SoficGroups.KunRootedIndicatorCrossing.exists_hyperfilter_gram_limit_of_pointwise_bound
    {I : Type*} {H : ℕ → Type*}
    [∀ n, SeminormedAddCommGroup (H n)]
    [∀ n, InnerProductSpace ℂ (H n)]
    (v : ∀ n, I → H n) (B : I → ℝ)
    (hbound : ∀ n i, ‖v n i‖ ≤ B i) :
    ∃ K : Matrix I I ℂ,
      ∀ i j, Tendsto (fun n => ⟪v n i, v n j⟫_ℂ)
        (Filter.hyperfilter ℕ) (𝓝 (K i j)) := by sorry
