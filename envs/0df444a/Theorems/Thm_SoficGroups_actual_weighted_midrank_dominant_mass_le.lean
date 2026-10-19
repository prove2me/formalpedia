-- Prove2me | Theorems.Thm_SoficGroups_actual_weighted_midrank_dominant_mass_le
-- name    : SoficGroups.actual_weighted_midrank_dominant_mass_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.999052+00:00
-- url     : https://prove2.me/theorems/dfe06d57-a1d4-48ba-854f-735a068007d5
-- title:
--   SoficGroups.actual_weighted_midrank_dominant_mass_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff

theorem SoficGroups.actual_weighted_midrank_dominant_mass_le
    {V ι : Type*}
    (I : Finset ι) (C : ι → Finset V) (b : V → ℤ) (j : ι → ℤ)
    (hC : ∀ i ∈ I, (C i).Nonempty)
    (hmax : ∀ i ∈ I, ∀ k ∈ (C i).image b,
      componentRankMass (C i) b k ≤ componentRankMass (C i) b (j i)) :
    (∑ i ∈ I,
      (((C i).card - ((C i).filter fun x => b x = j i).card : ℕ) : ℝ)) ≤
      12 * ∑ i ∈ I,
        ((C i).card : ℝ) *
          midrankVariance (componentRankMassList (C i) b) := by sorry
