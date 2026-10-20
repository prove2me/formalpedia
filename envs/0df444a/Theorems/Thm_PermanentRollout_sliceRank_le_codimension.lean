-- Prove2me | Theorems.Thm_PermanentRollout_sliceRank_le_codimension
-- name    : PermanentRollout.sliceRank_le_codimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/6f0e68c3-2e84-4ff8-8213-1605c47bcf18
-- title:
--   PermanentRollout.sliceRank_le_codimension
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout

theorem PermanentRollout.sliceRank_le_codimension {n d dimension : ℕ}
    (hd : 3 ≤ d) (hn : 6 * blockWidth d ≤ n)
    (hscale : 4 * powerSumParameter d ≤ blockWidth d * blockColumns n d)
    (hdimension : dimension ≤ blockCount n d *
      (powerSumParameter d + blockColumns n d * (d - 2))) :
    sliceRank n d ≤ blockVariables n d - dimension := by sorry
