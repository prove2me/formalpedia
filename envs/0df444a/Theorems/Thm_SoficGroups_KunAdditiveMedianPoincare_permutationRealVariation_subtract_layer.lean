-- Prove2me | Theorems.Thm_SoficGroups_KunAdditiveMedianPoincare_permutationRealVariation_subtract_layer
-- name    : SoficGroups.KunAdditiveMedianPoincare.permutationRealVariation_subtract_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/23d6d881-2be0-4055-b940-6a4f4b55905b
-- title:
--   SoficGroups.KunAdditiveMedianPoincare.permutationRealVariation_subtract_layer
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunAdditiveMedianPoincare
open SoficGroups.CheegerPoincare
open Filter Topology
open scoped BigOperators

theorem SoficGroups.KunAdditiveMedianPoincare.permutationRealVariation_subtract_layer
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (f : V → ℝ)
    (A : Finset V) (m : ℝ) (hm : 0 ≤ m)
    (hinside : ∀ x ∈ A, m ≤ f x)
    (houtside : ∀ x, x ∉ A → f x = 0) :
    permutationRealVariation σ f =
      permutationRealVariation σ
        (fun x => if x ∈ A then f x - m else 0) +
        2 * m * (SoficGroups.boundary σ A : ℝ) := by sorry
