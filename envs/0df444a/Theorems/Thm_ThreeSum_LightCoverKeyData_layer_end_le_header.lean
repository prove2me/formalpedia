-- Prove2me | Theorems.Thm_ThreeSum_LightCoverKeyData_layer_end_le_header
-- name    : ThreeSum.LightCoverKeyData.layer_end_le_header
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:38:13.676032+00:00
-- url     : https://prove2.me/theorems/74db3fe8-8f1f-4dca-90d2-f86f7e172633
-- title:
--   Light Cover Key Data: layer end le header
-- statement:
--   The Light Cover Key Data construction uses the layer end le header property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverKeyData.lean#L25-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverKeyData.lean#L25-L28

import Definitions.Def_Submission_ThreeSum_LightCoverKeys
import Definitions.Def_Submission_ThreeSum_LightCoverKeyData
set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverKeyData
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000

theorem ThreeSum.LightCoverKeyData.layer_end_le_header (free h J : ℕ) :
    LightCoverKeys.afterCover free h+outputCount (512*h) h ≤ LightCoverKeys.keyHeader free h J := by sorry
