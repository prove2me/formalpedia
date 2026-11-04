-- Prove2me | Theorems.Thm_ThreeSum_LightCoverKeyData_free_le_keyEnd
-- name    : ThreeSum.LightCoverKeyData.free_le_keyEnd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:26:44.100168+00:00
-- url     : https://prove2.me/theorems/d5b4245e-ad6b-4829-b234-1a6576054d68
-- title:
--   Light Cover Key Data: free le key End
-- statement:
--   The Light Cover Key Data construction uses the free le key End property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverKeyData.lean#L35-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverKeyData.lean#L35-L39

import Definitions.Def_Submission_ThreeSum_LightCoverKeys
import Definitions.Def_Submission_ThreeSum_LightCoverKeyData
set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverKeyData
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000

theorem ThreeSum.LightCoverKeyData.free_le_keyEnd (free h J : ℕ) : free ≤ keyEnd free h J := by sorry
