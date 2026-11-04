-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorStageCosts_finish_le
-- name    : ThreeSum.EncodedColorStageCosts.finish_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:19:54.990205+00:00
-- url     : https://prove2.me/theorems/872b9372-74f5-4e58-ba49-6c9dc23e665c
-- title:
--   Encoded Color Stage Costs: finish le
-- statement:
--   The Encoded Color Stage Costs construction uses the finish le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorStageCosts.lean#L74-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorStageCosts.lean#L74-L80

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Theorems.Thm_ThreeSum_SourceFiniteCosts_finish_le

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorStageCosts
open Scales BandScales ArithmeticStageBounds

theorem ThreeSum.EncodedColorStageCosts.finish_le {base bound NL NR n : ℕ} (hn : 0 < n)
    (hb : base ≤ bound) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤ SourceFiniteCosts.finish bound n := by sorry
