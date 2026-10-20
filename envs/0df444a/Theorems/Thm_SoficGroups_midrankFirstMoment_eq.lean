-- Prove2me | Theorems.Thm_SoficGroups_midrankFirstMoment_eq
-- name    : SoficGroups.midrankFirstMoment_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.999052+00:00
-- url     : https://prove2.me/theorems/5ce648b0-b5a8-43bd-abb5-7ee356b1e2e1
-- title:
--   SoficGroups.midrankFirstMoment_eq
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

theorem SoficGroups.midrankFirstMoment_eq (a : ℝ) (ps : List ℝ) :
    midrankFirstMoment a ps = ((a + ps.sum) ^ 2 - a ^ 2) / 2 := by sorry
