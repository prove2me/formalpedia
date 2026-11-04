-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixLoop_program_library
-- name    : ThreeSum.LightWeightedGlobalPrefixLoop.program_library
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:36:12.863914+00:00
-- url     : https://prove2.me/theorems/5f0a3a45-5287-449f-bdaf-c27d9ffa6dea
-- title:
--   Light Weighted Global Prefix Loop: program library
-- statement:
--   The Light Weighted Global Prefix Loop construction uses the program library property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixProgramLibrary.lean#L53-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixProgramLibrary.lean#L53-L62

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixLoop
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixProgramLibrary
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPrefixLoop
open Light
set_option maxHeartbeats 5000000

theorem ThreeSum.LightWeightedGlobalPrefixLoop.program_library (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) : Library (program p R S K raws words maps xl yl zl xr yr zr) := by sorry
