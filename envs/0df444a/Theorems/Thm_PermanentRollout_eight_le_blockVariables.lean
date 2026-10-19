-- Prove2me | Theorems.Thm_PermanentRollout_eight_le_blockVariables
-- name    : PermanentRollout.eight_le_blockVariables
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/544329e1-96db-4776-8f85-a0bc0496e645
-- title:
--   PermanentRollout.eight_le_blockVariables
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout

theorem PermanentRollout.eight_le_blockVariables {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n) : 8 ≤ blockVariables n d := by sorry
