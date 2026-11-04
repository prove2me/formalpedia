-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySourceCountHost_libraries_length
-- name    : ThreeSum.LightTernarySourceCountHost.libraries_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:16:59.593761+00:00
-- url     : https://prove2.me/theorems/d43741cc-6986-4d55-afb8-c6dc010ff1fb
-- title:
--   Light Ternary Source Count Host: libraries length
-- statement:
--   The Light Ternary Source Count Host construction uses the libraries length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L68-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L68-L71

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

theorem ThreeSum.LightTernarySourceCountHost.libraries_length (xl yl zl xr yr zr : List ℤ) :
    (libraries xl yl zl xr yr zr).length=122 := by sorry
