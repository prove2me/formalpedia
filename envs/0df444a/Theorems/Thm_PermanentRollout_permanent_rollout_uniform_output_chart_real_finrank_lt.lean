-- Prove2me | Theorems.Thm_PermanentRollout_permanent_rollout_uniform_output_chart_real_finrank_lt
-- name    : PermanentRollout.permanent_rollout_uniform_output_chart_real_finrank_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/25430a18-ee99-472a-9644-fbfba047a843
-- title:
--   PermanentRollout.permanent_rollout_uniform_output_chart_real_finrank_lt
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section

theorem PermanentRollout.permanent_rollout_uniform_output_chart_real_finrank_lt
    (k m : ℕ) :
    finrank ℝ (permanentRolloutUniformOutputChartDomain k m) <
      finrank ℝ (Fin (k + 1) → Fin (m + 1) → ℂ) := by sorry
