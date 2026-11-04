-- Prove2me | Theorems.Thm_ThreeSum_ColorBandBounds_count_le
-- name    : ThreeSum.ColorBandBounds.count_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:51:34.869719+00:00
-- url     : https://prove2.me/theorems/709d9ba4-32e2-45f1-b960-046600bd93aa
-- title:
--   Color Band Bounds: count le
-- statement:
--   The Color Band Bounds construction uses the count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorBandBounds.lean#L21-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorBandBounds.lean#L21-L23

import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
import Definitions.Def_Submission_ThreeSum_ColorBandBounds
set_option autoImplicit false
open ThreeSum ThreeSum.ColorBandBounds
open BandPartition
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

theorem ThreeSum.ColorBandBounds.count_le {a b c n g : ℕ} (hlen : a+b+c=n) :
    LightBandEnumeration.count (size a g) (size b g) (size c g) ≤ count n g := by sorry
