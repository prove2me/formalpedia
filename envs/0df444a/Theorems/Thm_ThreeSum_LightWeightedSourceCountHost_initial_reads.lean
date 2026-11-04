-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_initial_reads
-- name    : ThreeSum.LightWeightedSourceCountHost.initial_reads
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:28:26.713024+00:00
-- url     : https://prove2.me/theorems/e953837b-165a-4a26-9e4f-62b5a5c707e4
-- title:
--   Light Weighted Source Count Host: initial reads
-- statement:
--   The Light Weighted Source Count Host construction uses the initial reads property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L103-L122
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L103-L122

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

theorem ThreeSum.LightWeightedSourceCountHost.initial_reads (left right frontend : List ℤ)
    (hl : left.length=23) (hr : right.length=23) :
    Reads (frame (args left right frontend)) 0 left ∧
    Reads (frame (args left right frontend)) 23 right ∧
    Reads (frame (args left right frontend)) 46 frontend := by sorry
