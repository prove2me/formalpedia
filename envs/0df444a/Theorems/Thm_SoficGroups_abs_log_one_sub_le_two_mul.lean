-- Prove2me | Theorems.Thm_SoficGroups_abs_log_one_sub_le_two_mul
-- name    : SoficGroups.abs_log_one_sub_le_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.999052+00:00
-- url     : https://prove2.me/theorems/b8491e81-4769-46a7-9779-8e47bc37b93e
-- title:
--   SoficGroups.abs_log_one_sub_le_two_mul
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

theorem SoficGroups.abs_log_one_sub_le_two_mul
    (eta : ℝ) (heta0 : 0 ≤ eta) (hetaHalf : eta ≤ (1 : ℝ) / 2) :
    |Real.log (1 - eta)| ≤ 2 * eta := by sorry
