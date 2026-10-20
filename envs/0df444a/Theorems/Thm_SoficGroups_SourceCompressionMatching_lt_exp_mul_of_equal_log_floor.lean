-- Prove2me | Theorems.Thm_SoficGroups_SourceCompressionMatching_lt_exp_mul_of_equal_log_floor
-- name    : SoficGroups.SourceCompressionMatching.lt_exp_mul_of_equal_log_floor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/563a1616-5852-4c7c-886b-9a5586a55a0a
-- title:
--   SoficGroups.SourceCompressionMatching.lt_exp_mul_of_equal_log_floor
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionMatching
open Filter Topology
open scoped BigOperators symmDiff

theorem SoficGroups.SourceCompressionMatching.lt_exp_mul_of_equal_log_floor
    {x y H r : ℝ} (hx : 0 < x) (hy : 0 < y) (hH : 0 < H)
    (hrank :
      ⌊(Real.log x + r) / H⌋ = ⌊(Real.log y + r) / H⌋) :
    y < Real.exp H * x := by sorry
