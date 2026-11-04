-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryRank_partialRank_le
-- name    : ThreeSum.LightTernaryRank.partialRank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:49:54.178566+00:00
-- url     : https://prove2.me/theorems/050ef37e-b6cc-49cd-ac13-1945a715e62e
-- title:
--   Light Ternary Rank: partial Rank le
-- statement:
--   The Light Ternary Rank construction uses the partial Rank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRank.lean#L18-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRank.lean#L18-L25

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryRank
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRank
open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress

theorem ThreeSum.LightTernaryRank.partialRank_le (N m j : ℕ) : partialRank N m j ≤ 2*j := by sorry
