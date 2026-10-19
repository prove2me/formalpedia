-- Prove2me | Theorems.Thm_SoficGroups_sum_map_sort_eq
-- name    : SoficGroups.sum_map_sort_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.999052+00:00
-- url     : https://prove2.me/theorems/7c5e7a43-3c05-4fa0-81e0-1a5d6bff582b
-- title:
--   SoficGroups.sum_map_sort_eq
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

theorem SoficGroups.sum_map_sort_eq {α : Type*}
    [LinearOrder α]
    (s : Finset α) (f : α → ℝ) :
    ((s.sort (· ≤ ·)).map f).sum = ∑ a ∈ s, f a := by sorry
