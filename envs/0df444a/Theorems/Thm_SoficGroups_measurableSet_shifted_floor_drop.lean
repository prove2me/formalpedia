-- Prove2me | Theorems.Thm_SoficGroups_measurableSet_shifted_floor_drop
-- name    : SoficGroups.measurableSet_shifted_floor_drop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.999052+00:00
-- url     : https://prove2.me/theorems/04c460bd-cfb1-44a4-8dab-5cc57d51ae43
-- title:
--   SoficGroups.measurableSet_shifted_floor_drop
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

theorem SoficGroups.measurableSet_shifted_floor_drop (u v H : ℝ) :
    MeasurableSet
      {r : ℝ | ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋} := by sorry
