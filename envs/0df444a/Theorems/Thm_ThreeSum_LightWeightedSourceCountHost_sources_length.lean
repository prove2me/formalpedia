-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_sources_length
-- name    : ThreeSum.LightWeightedSourceCountHost.sources_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:22:12.750135+00:00
-- url     : https://prove2.me/theorems/9a820965-7a93-41d1-a0cf-2acd7ecabea8
-- title:
--   Light Weighted Source Count Host: sources length
-- statement:
--   The Light Weighted Source Count Host construction uses the sources length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L68-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L68-L71

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_Submission_Weighted_SourceCountHost
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedSourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedSourceCountHost.sources_length (xl yl zl xr yr zr : List ℤ) :
    (sources xl yl zl xr yr zr).length=70 := by sorry
