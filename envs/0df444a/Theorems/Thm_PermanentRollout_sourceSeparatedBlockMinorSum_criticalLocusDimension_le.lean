-- Prove2me | Theorems.Thm_PermanentRollout_sourceSeparatedBlockMinorSum_criticalLocusDimension_le
-- name    : PermanentRollout.sourceSeparatedBlockMinorSum_criticalLocusDimension_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/184dc773-c83d-45c4-98e4-9f13d34847a0
-- title:
--   PermanentRollout.sourceSeparatedBlockMinorSum_criticalLocusDimension_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section

theorem PermanentRollout.sourceSeparatedBlockMinorSum_criticalLocusDimension_le
    {n d : ℕ} (hd : 3 ≤ d)
    (weight : Fin (blockCount n d) → ℂ)
    (hw : ∀ h, weight h ≠ 0) :
    criticalLocusDimension (sourceSeparatedBlockMinorSum n d weight) ≤
      ((blockCount n d *
        (powerSumParameter d + blockColumns n d * (d - 2)) : ℕ) :
          WithBot ℕ∞) := by sorry
