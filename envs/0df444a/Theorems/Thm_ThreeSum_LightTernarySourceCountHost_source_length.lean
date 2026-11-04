-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySourceCountHost_source_length
-- name    : ThreeSum.LightTernarySourceCountHost.source_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:16:57.624432+00:00
-- url     : https://prove2.me/theorems/a0ee6efb-bddb-4aa4-83c3-8a018750b221
-- title:
--   Light Ternary Source Count Host: source length
-- statement:
--   The Light Ternary Source Count Host construction uses the source length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L54-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L54-L61

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

theorem ThreeSum.LightTernarySourceCountHost.source_length (x y z : List ℤ) :
    (LightTernarySourceHost.program x y z).length=35 := by sorry
