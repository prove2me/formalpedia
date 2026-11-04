-- Prove2me | Theorems.Thm_ThreeSum_LightRadixKeys_space_bound_w3sum_ac885d1
-- name    : ThreeSum.LightRadixKeys.space_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:18:23.591613+00:00
-- url     : https://prove2.me/theorems/8cc1a2ac-75fc-4b58-b0b3-f0200731e4bb
-- title:
--   Light Radix Keys: space bound
-- statement:
--   The Light Radix Keys construction uses the space bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixKeys.lean#L47-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixKeys.lean#L47-L61

import Definitions.Def_Submission_ThreeSum_LightRadixRows
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixKeys
open Light RadixKeyLists
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

theorem ThreeSum.LightRadixKeys.space_bound_w3sum_ac885d1 (dst m J : ℕ) (hm : 1 ≤ m) :
    space dst m J ≤ dst+(J+1)*(m^J+1) := by sorry
