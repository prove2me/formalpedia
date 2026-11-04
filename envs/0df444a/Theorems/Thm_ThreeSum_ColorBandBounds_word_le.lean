-- Prove2me | Theorems.Thm_ThreeSum_ColorBandBounds_word_le
-- name    : ThreeSum.ColorBandBounds.word_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:51:34.668912+00:00
-- url     : https://prove2.me/theorems/9e31e07d-b680-4b73-a2c8-4e8e63092f88
-- title:
--   Color Band Bounds: word le
-- statement:
--   The Color Band Bounds construction uses the word le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorBandBounds.lean#L49-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorBandBounds.lean#L49-L55

import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
import Definitions.Def_Submission_ThreeSum_ColorBandBounds
set_option autoImplicit false
open ThreeSum ThreeSum.ColorBandBounds
open BandPartition
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

theorem ThreeSum.ColorBandBounds.word_le {a b c n g U : ℕ} (hlen : a+b+c=n) :
    LightBandPreprocessing.word a b c g U ≤ word n g U := by sorry
