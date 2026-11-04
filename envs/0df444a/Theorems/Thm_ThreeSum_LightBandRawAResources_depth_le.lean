-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawAResources_depth_le
-- name    : ThreeSum.LightBandRawAResources.depth_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:32.514813+00:00
-- url     : https://prove2.me/theorems/1fe7562c-1300-4f89-aa0f-216068cabfa6
-- title:
--   Light Band Raw AResources: depth le
-- statement:
--   The Light Band Raw AResources construction uses the depth le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAResources.lean#L57-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAResources.lean#L57-L61

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_LightBandRawAResources
import Theorems.Thm_ThreeSum_ColorBandBounds_depth_le

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAResources
open Light EncodedColorLayout
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

theorem ThreeSum.LightBandRawAResources.depth_le (W n g : ℕ) : LightBandRawAColor.depth W n g ≤ W+5*n+21 := by sorry
