-- Prove2me | Theorems.Thm_WeightedRace_bound
-- name    : WeightedRace.bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T05:00:08.442644+00:00
-- url     : https://prove2.me/theorems/37442c5d-cbbf-4a07-ad33-14357e1cbe53
-- title:
--   Weighted Race: bound
-- statement:
--   The Weighted Race construction uses the bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted.lean#L7-L8
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted.lean#L7-L8

import Definitions.Def_Submission_Weighted_Global_TernaryFinalSolver
import Definitions.Def_Submission_Weighted
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTime_bound
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceValues_bound

set_option autoImplicit false
open WeightedRace

theorem WeightedRace.bound : EndStatement.ThreeSum.SolvedInTime (96013971 / 50000000 : Rat) := by sorry
