-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixLoop_program_eq_controller_append
-- name    : ThreeSum.LightWeightedGlobalPrefixLoop.program_eq_controller_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:35:53.511072+00:00
-- url     : https://prove2.me/theorems/30cf75c7-d99f-4a69-9ff0-091d6756dcc3
-- title:
--   Light Weighted Global Prefix Loop: program eq controller append
-- statement:
--   The Light Weighted Global Prefix Loop construction uses the program eq controller append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixProgramLibrary.lean#L23-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixProgramLibrary.lean#L23-L27

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixLoop
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixProgramLibrary
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPrefixLoop
open Light
set_option maxHeartbeats 5000000

theorem ThreeSum.LightWeightedGlobalPrefixLoop.program_eq_controller_append (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) :
    program p R S K raws words maps xl yl zl xr yr zr=
      LightWeightedGlobalSeedController.program p R S K raws words maps xl yl zl xr yr zr++tail := by sorry
