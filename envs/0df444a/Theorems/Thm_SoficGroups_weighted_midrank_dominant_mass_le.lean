-- Prove2me | Theorems.Thm_SoficGroups_weighted_midrank_dominant_mass_le
-- name    : SoficGroups.weighted_midrank_dominant_mass_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.999052+00:00
-- url     : https://prove2.me/theorems/31e19c87-1135-494f-a704-a29f642f8140
-- title:
--   SoficGroups.weighted_midrank_dominant_mass_le
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

theorem SoficGroups.weighted_midrank_dominant_mass_le {ι : Type*}
    (I : Finset ι) (weight : ι → ℝ)
    (q : ι → List ℝ) (m : ι → ℝ)
    (hweight : ∀ i ∈ I, 0 ≤ weight i)
    (hsum : ∀ i ∈ I, (q i).sum = 1)
    (hpositive : ∀ i ∈ I, ∀ x ∈ q i, 0 ≤ x)
    (hdominant : ∀ i ∈ I, ∀ x ∈ q i, x ≤ m i) :
    (∑ i ∈ I, weight i * (1 - m i)) ≤
      12 * ∑ i ∈ I, weight i * midrankVariance (q i) := by sorry
