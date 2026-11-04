-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_callArgs_values
-- name    : ThreeSum.LightWeightedSourceCountHost.callArgs_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:24:38.329748+00:00
-- url     : https://prove2.me/theorems/649acd25-28e0-4e2e-935d-b73de4af365b
-- title:
--   Light Weighted Source Count Host: call Args values
-- statement:
--   The Light Weighted Source Count Host construction uses the call Args values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L90-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L90-L97

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_Submission_Weighted_SourceCountHost
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedSourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedSourceCountHost.callArgs_values (loc μ : ℕ → ℤ) (offset count : ℕ) (vals : List ℤ)
    (hlen : vals.length=count) (hread : Reads loc offset vals) :
    (callArgs offset count).map (·.val ⟨loc,μ⟩)=vals := by sorry
