-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_offset_lt
-- name    : ThreeSum.WeightedGlobalArenaLayout.offset_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:32:08.806968+00:00
-- url     : https://prove2.me/theorems/b3918525-8148-4f33-b66f-71782701fddd
-- title:
--   Weighted Global Arena Layout: offset lt
-- statement:
--   The Weighted Global Arena Layout construction uses the offset lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaLayout.lean#L105-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaLayout.lean#L105-L108

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_SourceCountHost
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Theorems.Thm_ThreeSum_LightBalancedOffset_offset_lt

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalArenaLayout

theorem ThreeSum.WeightedGlobalArenaLayout.offset_lt {free C slot len offset : ℕ} (hoff : offset<len) (hlen : len≤C) :
    addr free C slot+offset<addr free C (slot+1) := by sorry
