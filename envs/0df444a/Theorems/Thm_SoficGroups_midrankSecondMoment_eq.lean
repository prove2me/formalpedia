-- Prove2me | Theorems.Thm_SoficGroups_midrankSecondMoment_eq
-- name    : SoficGroups.midrankSecondMoment_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.999052+00:00
-- url     : https://prove2.me/theorems/3b8fa0f4-0ea5-4385-9ea8-476523553b60
-- title:
--   SoficGroups.midrankSecondMoment_eq
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

theorem SoficGroups.midrankSecondMoment_eq (a : ℝ) (ps : List ℝ) :
    midrankSecondMoment a ps =
      ((a + ps.sum) ^ 3 - a ^ 3) / 3 -
        (ps.map fun p => p ^ 3).sum / 12 := by sorry
