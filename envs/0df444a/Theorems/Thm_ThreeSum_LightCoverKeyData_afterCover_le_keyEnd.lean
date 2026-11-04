-- Prove2me | Theorems.Thm_ThreeSum_LightCoverKeyData_afterCover_le_keyEnd
-- name    : ThreeSum.LightCoverKeyData.afterCover_le_keyEnd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:34:00.860363+00:00
-- url     : https://prove2.me/theorems/23d3b3aa-cce3-45e2-8c49-c69c53a26852
-- title:
--   Light Cover Key Data: after Cover le key End
-- statement:
--   The Light Cover Key Data construction uses the after Cover le key End property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverKeyData.lean#L30-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverKeyData.lean#L30-L33

import Definitions.Def_Submission_ThreeSum_LightCoverKeys
import Definitions.Def_Submission_ThreeSum_LightCoverKeyData
set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverKeyData
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000

theorem ThreeSum.LightCoverKeyData.afterCover_le_keyEnd (free h J : ℕ) : LightCoverKeys.afterCover free h ≤ keyEnd free h J := by sorry
