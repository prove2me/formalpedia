-- Prove2me | Theorems.Thm_ThreeSum_ColorBandBounds_time_le
-- name    : ThreeSum.ColorBandBounds.time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:51:34.703315+00:00
-- url     : https://prove2.me/theorems/1d1549b9-a1db-49b2-a64a-6969895a6ced
-- title:
--   Color Band Bounds: time le
-- statement:
--   The Color Band Bounds construction uses the time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorBandBounds.lean#L30-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorBandBounds.lean#L30-L40

import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
import Definitions.Def_Submission_ThreeSum_ColorBandBounds
import Theorems.Thm_ThreeSum_LightKaratsuba_time_le

set_option autoImplicit false
open ThreeSum ThreeSum.ColorBandBounds
open BandPartition
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

theorem ThreeSum.ColorBandBounds.time_le {a b c n g : ℕ} (hlen : a+b+c=n) :
    LightBandPreprocessing.time a b c g ≤ time n g := by sorry
