-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixCommit_keys
-- name    : ThreeSum.WeightedGlobalArenaPrefixCommit.keys
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:54:54.871835+00:00
-- url     : https://prove2.me/theorems/eb97ad3e-3cb0-40c6-804d-002ce7b3a0b4
-- title:
--   Weighted Global Arena Prefix Commit: keys
-- statement:
--   The retained keys are the exact append results of the selected replay.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixCommit.lean#L37-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixCommit.lean#L37-L45

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixFinish
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixCommit
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixFinish

theorem ThreeSum.WeightedGlobalArenaPrefixCommit.keys {C : Config} {D : Data C} {R S rows newSpan : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {ξ ν : ℕ→ℤ}
    (H : Committed C rows newSpan ξ ν)
    (O : LightWeightedGlobalSeedScoreFull.Outputs C D R S raws words maps ξ) :
    Reads ν C.Bold C.nB D.newB ∧ Reads ν C.Cold C.nC D.newC ∧ Reads ν C.Oold C.nO D.newO := by sorry
