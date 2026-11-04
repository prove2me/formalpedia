-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update
-- name    : ThreeSum.LightWeightedSourceCountHost.Reads.update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:23:00.806535+00:00
-- url     : https://prove2.me/theorems/0fa90d1d-b730-41d4-95b3-65077424b725
-- title:
--   Reads: update
-- statement:
--   The Reads construction uses the update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L124-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L124-L129

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_Submission_Weighted_SourceCountHost
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedSourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedSourceCountHost.Reads.update {loc : ℕ → ℤ} {offset x : ℕ} {vals : List ℤ}
    (h : Reads loc offset vals) (hx : offset+vals.length≤x) (r : ℤ) :
    Reads (Function.update loc x r) offset vals := by sorry
