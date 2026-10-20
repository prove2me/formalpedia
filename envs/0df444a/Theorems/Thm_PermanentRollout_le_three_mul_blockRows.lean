-- Prove2me | Theorems.Thm_PermanentRollout_le_three_mul_blockRows
-- name    : PermanentRollout.le_three_mul_blockRows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/d1fce9a4-d247-42db-a1c2-29151c66a31a
-- title:
--   PermanentRollout.le_three_mul_blockRows
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout

theorem PermanentRollout.le_three_mul_blockRows {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n) : n ≤ 3 * blockRows n d := by sorry
