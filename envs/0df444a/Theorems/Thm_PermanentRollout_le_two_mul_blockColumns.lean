-- Prove2me | Theorems.Thm_PermanentRollout_le_two_mul_blockColumns
-- name    : PermanentRollout.le_two_mul_blockColumns
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/50c271a2-98f8-4106-a54f-bbd527d2ab9c
-- title:
--   PermanentRollout.le_two_mul_blockColumns
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout

theorem PermanentRollout.le_two_mul_blockColumns (n d : ℕ) : n ≤ 2 * blockColumns n d := by sorry
