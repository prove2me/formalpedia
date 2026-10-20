-- Prove2me | Theorems.Thm_SoficGroups_matched_exists_le_weighted_average
-- name    : SoficGroups.matched_exists_le_weighted_average
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/48f632a7-52ba-4b3c-a487-8380f2577913
-- title:
--   SoficGroups.matched_exists_le_weighted_average
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

theorem SoficGroups.matched_exists_le_weighted_average {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (weight bad : ι → ℝ)
    (hweight : ∀ i ∈ s, 0 < weight i) :
    ∃ i ∈ s,
      bad i / weight i ≤ (∑ j ∈ s, bad j) / (∑ j ∈ s, weight j) := by sorry
