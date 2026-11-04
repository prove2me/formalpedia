-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixCommit_layout
-- name    : ThreeSum.WeightedGlobalArenaPrefixCommit.layout
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:56:25.03177+00:00
-- url     : https://prove2.me/theorems/d662d29a-79f6-40e2-ba9c-5f71b621ee4a
-- title:
--   Weighted Global Arena Prefix Commit: layout
-- statement:
--   Fixed slots discharge every actual key/span commit separation.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixCommit.lean#L17-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixCommit.lean#L17-L34

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixFinish
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_layout
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixCommit
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixFinish

theorem ThreeSum.WeightedGlobalArenaPrefixCommit.layout (p r rows : ℕ) (I : Input) (A : Inputs) {lim : Limits}
    (h48 : 48≤I.capacity) (hB : I.nB≤I.capacity) (hC : I.nC≤I.capacity)
    (hO : I.requesterCount≤I.capacity) (hSpan : rows*A.J≤I.capacity)
    (hspace : finish I.free I.capacity≤lim.space) :
    Layout (config p r I A 0) lim (addr I.free I.capacity 3) rows (addr I.free I.capacity 8) := by sorry
