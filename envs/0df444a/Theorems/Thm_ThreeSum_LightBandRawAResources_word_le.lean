-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawAResources_word_le
-- name    : ThreeSum.LightBandRawAResources.word_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:52.158747+00:00
-- url     : https://prove2.me/theorems/084303e6-295c-4556-b91d-e1a6b5b0d47b
-- title:
--   Light Band Raw AResources: word le
-- statement:
--   The Light Band Raw AResources construction uses the word le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAResources.lean#L48-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAResources.lean#L48-L55

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_LightBandRawAResources
import Theorems.Thm_ThreeSum_ColorBandBounds_word_le

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAResources
open Light EncodedColorLayout
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

theorem ThreeSum.LightBandRawAResources.word_le (W n g U : ℕ) :
    LightBandRawAColor.word W n g U ≤ 2^(W+1)+3*n^2+29*n+2*g+9*U+100 := by sorry
