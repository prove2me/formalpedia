-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_exists_hyperfilter_positive_gram_kernel_of_pointwise_bound
-- name    : SoficGroups.KunRootedIndicatorCrossing.exists_hyperfilter_positive_gram_kernel_of_pointwise_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/0ea4d848-8950-411f-ad63-7316012cff52
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.exists_hyperfilter_positive_gram_kernel_of_pointwise_bound
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

theorem SoficGroups.KunRootedIndicatorCrossing.exists_hyperfilter_positive_gram_kernel_of_pointwise_bound
    {I : Type*} {H : ℕ → Type*}
    [∀ n, SeminormedAddCommGroup (H n)]
    [∀ n, InnerProductSpace ℂ (H n)]
    (v : ∀ n, I → H n) (B : I → ℝ)
    (hbound : ∀ n i, ‖v n i‖ ≤ B i) :
    ∃ K : Matrix I I ℂ,
      K.PosSemidef ∧
      ∀ i j, Tendsto (fun n => ⟪v n i, v n j⟫_ℂ)
        (Filter.hyperfilter ℕ) (𝓝 (K i j)) := by sorry
