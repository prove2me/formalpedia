-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySourceCountHost_callArgs_values
-- name    : ThreeSum.LightTernarySourceCountHost.callArgs_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:17:22.831118+00:00
-- url     : https://prove2.me/theorems/8593362a-81cb-4c2c-b647-ff39f111f6b3
-- title:
--   Light Ternary Source Count Host: call Args values
-- statement:
--   The Light Ternary Source Count Host construction uses the call Args values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L85-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L85-L92

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

theorem ThreeSum.LightTernarySourceCountHost.callArgs_values (loc μ : ℕ → ℤ) (offset count : ℕ) (vals : List ℤ)
    (hlen : vals.length=count) (hread : Reads loc offset vals) :
    (callArgs offset count).map (·.val ⟨loc,μ⟩)=vals := by sorry
