-- Prove2me | Theorems.Thm_ThreeSum_ColorBandBounds_width_le
-- name    : ThreeSum.ColorBandBounds.width_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:51:25.353083+00:00
-- url     : https://prove2.me/theorems/631c3da9-9d3f-4ad7-8c42-1ec1aef61368
-- title:
--   Color Band Bounds: width le
-- statement:
--   The Color Band Bounds construction uses the width le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorBandBounds.lean#L25-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorBandBounds.lean#L25-L28

import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
import Definitions.Def_Submission_ThreeSum_ColorBandBounds
set_option autoImplicit false
open ThreeSum ThreeSum.ColorBandBounds
open BandPartition
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

theorem ThreeSum.ColorBandBounds.width_le {a b c n g : ℕ} (hlen : a+b+c=n) :
    LightBandEnumeration.width (size a g) (size b g) (size c g) ≤ width n g := by sorry
