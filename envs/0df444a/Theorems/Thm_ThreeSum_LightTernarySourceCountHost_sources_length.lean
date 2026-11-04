-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySourceCountHost_sources_length
-- name    : ThreeSum.LightTernarySourceCountHost.sources_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:16:40.735215+00:00
-- url     : https://prove2.me/theorems/b5d81847-924c-4853-9112-076c819cbed0
-- title:
--   Light Ternary Source Count Host: sources length
-- statement:
--   The Light Ternary Source Count Host construction uses the sources length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L63-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L63-L66

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

theorem ThreeSum.LightTernarySourceCountHost.sources_length (xl yl zl xr yr zr : List ℤ) :
    (sources xl yl zl xr yr zr).length=70 := by sorry
