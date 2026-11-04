-- Prove2me | Theorems.Thm_ThreeSum_LightRadixKeys_time_bound_w3sum_ac885d1
-- name    : ThreeSum.LightRadixKeys.time_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:18:45.908773+00:00
-- url     : https://prove2.me/theorems/4464d918-f5aa-49eb-8a61-321776fc68c4
-- title:
--   Light Radix Keys: time bound
-- statement:
--   The Light Radix Keys construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixKeys.lean#L63-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixKeys.lean#L63-L82

import Definitions.Def_Submission_ThreeSum_LightRadixRows
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Theorems.Thm_ThreeSum_LightRadixRows_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixKeys
open Light RadixKeyLists
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

theorem ThreeSum.LightRadixKeys.time_bound_w3sum_ac885d1 (m J : ℕ) (hm : 1 ≤ m) :
    time m J ≤ 300*(J+1)*(m^J+1) := by sorry
