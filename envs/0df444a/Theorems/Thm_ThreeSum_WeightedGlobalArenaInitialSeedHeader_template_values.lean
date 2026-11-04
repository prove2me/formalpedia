-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaInitialSeedHeader_template_values
-- name    : ThreeSum.WeightedGlobalArenaInitialSeedHeader.template_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:19:00.099717+00:00
-- url     : https://prove2.me/theorems/61987a02-db59-469a-86d3-cbe0019da706
-- title:
--   Weighted Global Arena Initial Seed Header: template values
-- statement:
--   Exact equality of the actual arena constructor's 48 seed fields.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaInitialSeedHeader.lean#L61-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaInitialSeedHeader.lean#L61-L68

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryArenaInitialSeedHeader
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaInitialSeedHeader
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixHeader LightWeightedGlobalPrefixFinish
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaInitialSeedHeader.template_values (I : Input) (A : Inputs) (p U wordRadix F q : ℕ) :
    LightWeightedGlobalArenaTemplate.seedValues
      (frame (LightWeightedGlobalArenaTemplate.args U I.free A.Bmatrix I.nB A.Cmatrix I.nC A.Omatrix I.requesterCount
        A.positions A.leftTagged A.rightTagged A.menu A.J p wordRadix F q 0 0 0 0 0 0)) I.free I.capacity=
      header (config p 0 I A 0) (q*q) 1 1 1 0 0 0 (addr I.free I.capacity 8) := by sorry
