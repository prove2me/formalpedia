-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySourceCountHost_callArgs_cost
-- name    : ThreeSum.LightTernarySourceCountHost.callArgs_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:17:00.960459+00:00
-- url     : https://prove2.me/theorems/666ed555-36c6-4b02-b2ca-f5e7b475166d
-- title:
--   Light Ternary Source Count Host: call Args cost
-- statement:
--   The Light Ternary Source Count Host construction uses the call Args cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L94-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L94-L96

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

theorem ThreeSum.LightTernarySourceCountHost.callArgs_cost (offset count : ℕ) :
    ((callArgs offset count).map Expr.cost).sum=count := by sorry
