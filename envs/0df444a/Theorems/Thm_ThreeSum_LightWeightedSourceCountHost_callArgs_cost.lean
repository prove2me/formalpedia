-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_callArgs_cost
-- name    : ThreeSum.LightWeightedSourceCountHost.callArgs_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:21:10.318814+00:00
-- url     : https://prove2.me/theorems/f39c2d65-2195-4dd9-8c5b-5fe5b384b885
-- title:
--   Light Weighted Source Count Host: call Args cost
-- statement:
--   The Light Weighted Source Count Host construction uses the call Args cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L99-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L99-L101

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

theorem ThreeSum.LightWeightedSourceCountHost.callArgs_cost (offset count : ℕ) :
    ((callArgs offset count).map Expr.cost).sum=count := by sorry
