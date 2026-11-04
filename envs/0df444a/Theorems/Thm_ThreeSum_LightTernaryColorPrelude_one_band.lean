-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryColorPrelude_one_band
-- name    : ThreeSum.LightTernaryColorPrelude.one_band
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:38:31.51011+00:00
-- url     : https://prove2.me/theorems/999cc32a-976b-4558-8064-98766ca299c8
-- title:
--   Light Ternary Color Prelude: one band
-- statement:
--   The Light Ternary Color Prelude construction uses the one band property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryColorPrelude.lean#L72-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryColorPrelude.lean#L72-L79

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightColorScanHost
import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryColorPrelude
open Light ColorClassLists LightColorParametersCosts
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000

theorem ThreeSum.LightTernaryColorPrelude.one_band {n : ℕ} (hn : 0<n) :
    BandPartition.size n n=1 ∧ ColorBandBounds.count n n=3 ∧ ColorBandBounds.width n n=2 := by sorry
