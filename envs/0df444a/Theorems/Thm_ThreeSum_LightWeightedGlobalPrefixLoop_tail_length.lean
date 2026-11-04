-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixLoop_tail_length
-- name    : ThreeSum.LightWeightedGlobalPrefixLoop.tail_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:37:08.905905+00:00
-- url     : https://prove2.me/theorems/77bf229c-67e4-4639-ac51-35967d5a308e
-- title:
--   Light Weighted Global Prefix Loop: tail length
-- statement:
--   The Light Weighted Global Prefix Loop construction uses the tail length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixProgramLibrary.lean#L29-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixProgramLibrary.lean#L29-L31

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixLoop
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixProgramLibrary
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPrefixLoop
open Light
set_option maxHeartbeats 5000000

theorem ThreeSum.LightWeightedGlobalPrefixLoop.tail_length : tail.length=18 := by sorry
