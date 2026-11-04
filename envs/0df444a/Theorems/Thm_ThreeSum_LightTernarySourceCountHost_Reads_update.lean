-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
-- name    : ThreeSum.LightTernarySourceCountHost.Reads.update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:17:02.239192+00:00
-- url     : https://prove2.me/theorems/000df59b-16ce-4abf-a22d-e9341a3bc45f
-- title:
--   Reads: update
-- statement:
--   The Reads construction uses the update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L119-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L119-L124

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_ThreeSum_LightTernaryCountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_Submission_ThreeSum_LightTernarySourceCountHost
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernarySourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightTernarySourceCountHost.Reads.update {loc : ℕ → ℤ} {offset x : ℕ} {vals : List ℤ}
    (h : Reads loc offset vals) (hx : offset+vals.length≤x) (r : ℤ) :
    Reads (Function.update loc x r) offset vals := by sorry
