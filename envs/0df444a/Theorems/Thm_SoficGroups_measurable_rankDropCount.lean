-- Prove2me | Theorems.Thm_SoficGroups_measurable_rankDropCount
-- name    : SoficGroups.measurable_rankDropCount
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.999052+00:00
-- url     : https://prove2.me/theorems/70ac9da5-b10a-4572-a127-821cc6b561bc
-- title:
--   SoficGroups.measurable_rankDropCount
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

theorem SoficGroups.measurable_rankDropCount {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H : ℝ) :
    Measurable (fun r : ℝ => rankDropCount u v H r) := by sorry
