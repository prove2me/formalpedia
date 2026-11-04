-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_args_length
-- name    : ThreeSum.LightWeightedSourceCountHost.args_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:21:33.303216+00:00
-- url     : https://prove2.me/theorems/7215ca76-5cae-49b0-87be-1a046e440a00
-- title:
--   Light Weighted Source Count Host: args length
-- statement:
--   The Light Weighted Source Count Host construction uses the args length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L55-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L55-L57

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

theorem ThreeSum.LightWeightedSourceCountHost.args_length (left right frontend : List ℤ)
    (hl : left.length=23) (hr : right.length=23) (hf : frontend.length=60) :
    (args left right frontend).length=106 := by sorry
