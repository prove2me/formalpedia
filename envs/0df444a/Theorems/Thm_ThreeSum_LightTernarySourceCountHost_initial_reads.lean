-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySourceCountHost_initial_reads
-- name    : ThreeSum.LightTernarySourceCountHost.initial_reads
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:18:20.03963+00:00
-- url     : https://prove2.me/theorems/ea578cc0-27bd-40ce-a5c6-14fc5f58c441
-- title:
--   Light Ternary Source Count Host: initial reads
-- statement:
--   The Light Ternary Source Count Host construction uses the initial reads property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L98-L117
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L98-L117

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

theorem ThreeSum.LightTernarySourceCountHost.initial_reads (left right frontend : List ℤ)
    (hl : left.length=23) (hr : right.length=23) :
    Reads (frame (args left right frontend)) 0 left ∧
    Reads (frame (args left right frontend)) 23 right ∧
    Reads (frame (args left right frontend)) 46 frontend := by sorry
