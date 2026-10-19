-- Prove2me | Theorems.Thm_PermanentRollout_blockVariables_eq_four_mul
-- name    : PermanentRollout.blockVariables_eq_four_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/137360d7-fa60-41de-8d8b-435efad8619f
-- title:
--   PermanentRollout.blockVariables_eq_four_mul
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout

theorem PermanentRollout.blockVariables_eq_four_mul (n d : ℕ) :
    blockVariables n d = 4 * (blockCount n d * blockColumns n d * d) := by sorry
