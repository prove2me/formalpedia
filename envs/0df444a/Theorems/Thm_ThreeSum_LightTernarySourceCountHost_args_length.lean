-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySourceCountHost_args_length
-- name    : ThreeSum.LightTernarySourceCountHost.args_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:16:27.233734+00:00
-- url     : https://prove2.me/theorems/6d63a754-c555-4c5b-a8c0-9d8d0e65cb2a
-- title:
--   Light Ternary Source Count Host: args length
-- statement:
--   The Light Ternary Source Count Host construction uses the args length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L50-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L50-L52

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_ThreeSum_LightTernaryCountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_Submission_ThreeSum_LightTernarySourceCountHost
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernarySourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightTernarySourceCountHost.args_length (left right frontend : List ℤ)
    (hl : left.length=23) (hr : right.length=23) (hf : frontend.length=60) :
    (args left right frontend).length=106 := by sorry
