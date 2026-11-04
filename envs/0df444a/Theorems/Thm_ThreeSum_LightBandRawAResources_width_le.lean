-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawAResources_width_le
-- name    : ThreeSum.LightBandRawAResources.width_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:59:06.398522+00:00
-- url     : https://prove2.me/theorems/f785f7cd-7e53-400e-8025-f67178931fff
-- title:
--   Light Band Raw AResources: width le
-- statement:
--   The Light Band Raw AResources construction uses the width le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAResources.lean#L42-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAResources.lean#L42-L46

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_LightBandRawAResources
import Theorems.Thm_ThreeSum_ColorBandBounds_width_le

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAResources
open Light EncodedColorLayout
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

theorem ThreeSum.LightBandRawAResources.width_le (n g : ℕ) : ColorBandBounds.width n g ≤ 3*n+1 := by sorry
