-- Prove2me | Theorems.Thm_PermanentRollout_exists_eventual_source_parameter_bounds
-- name    : PermanentRollout.exists_eventual_source_parameter_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/3513516a-699a-4660-9ace-a7fdf50a2ba2
-- title:
--   PermanentRollout.exists_eventual_source_parameter_bounds
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout

theorem PermanentRollout.exists_eventual_source_parameter_bounds {d : ℕ} (hd : 3 ≤ d) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      6 * blockWidth d ≤ n ∧
      8 * powerSumParameter d ≤ n * blockWidth d ∧
      4 * powerSumParameter d ≤ blockWidth d * blockColumns n d ∧
      8 ≤ blockVariables n d := by sorry
