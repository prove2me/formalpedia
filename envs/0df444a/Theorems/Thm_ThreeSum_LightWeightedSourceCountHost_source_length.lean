-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_source_length
-- name    : ThreeSum.LightWeightedSourceCountHost.source_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:21:09.858949+00:00
-- url     : https://prove2.me/theorems/c002c4ac-ef31-49c4-91d2-6128064d0c05
-- title:
--   Light Weighted Source Count Host: source length
-- statement:
--   The Light Weighted Source Count Host construction uses the source length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L59-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L59-L66

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

theorem ThreeSum.LightWeightedSourceCountHost.source_length (x y z : List ℤ) :
    (LightTernarySourceHost.program x y z).length=35 := by sorry
