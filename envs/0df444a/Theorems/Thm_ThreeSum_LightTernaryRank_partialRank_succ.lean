-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryRank_partialRank_succ
-- name    : ThreeSum.LightTernaryRank.partialRank_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:21:24.778929+00:00
-- url     : https://prove2.me/theorems/3d92dea6-963e-4425-9266-0e755703960d
-- title:
--   Light Ternary Rank: partial Rank succ
-- statement:
--   The Light Ternary Rank construction uses the partial Rank succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRank.lean#L15-L16
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRank.lean#L15-L16

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryRank
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRank
open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress

theorem ThreeSum.LightTernaryRank.partialRank_succ (N m j : ℕ) :
    partialRank N m (j+1)=partialRank N m j+digitAt N m j := by sorry
