-- Prove2me | Theorems.Thm_ThreeSum_LightCoverKeyData_keyEnd_le_space
-- name    : ThreeSum.LightCoverKeyData.keyEnd_le_space
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:05:07.62655+00:00
-- url     : https://prove2.me/theorems/f1cf85d0-2842-4572-9d48-aad9534d71cb
-- title:
--   Light Cover Key Data: key End le space
-- statement:
--   The Light Cover Key Data construction uses the key End le space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverKeyData.lean#L41-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverKeyData.lean#L41-L45

import Definitions.Def_Submission_ThreeSum_LightCoverKeys
import Definitions.Def_Submission_ThreeSum_LightCoverKeyData
set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverKeyData
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000

theorem ThreeSum.LightCoverKeyData.keyEnd_le_space (free h J : ℕ) : keyEnd free h J ≤ LightCoverKeys.space free h J := by sorry
