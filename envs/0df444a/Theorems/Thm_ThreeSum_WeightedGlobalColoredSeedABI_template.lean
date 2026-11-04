-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredSeedABI_template
-- name    : ThreeSum.WeightedGlobalColoredSeedABI.template
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:27:53.587199+00:00
-- url     : https://prove2.me/theorems/9e9dffd6-b01e-47dd-967e-d5735a5551ad
-- title:
--   Weighted Global Colored Seed ABI: template
-- statement:
--   The actual runtime twenty-three inputs, including duplicate signed/tagged
--   matrix pointers, yield the canonical seed template.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSeedABI.lean#L33-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSeedABI.lean#L33-L39

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredInitializationProof
import Definitions.Def_Submission_Weighted_Global_TernaryArenaInitialSeedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSeedABI
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredSeedABI
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixFinish
open LightWeightedGlobalColoredInitializationProof
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalColoredSeedABI.template (I : Input) (A : Inputs) (p n U R F q : ℕ)
    (hleft : A.leftTagged=A.Bmatrix) (hright : A.rightTagged=A.Cmatrix) :
    LightWeightedGlobalArenaTemplate.seedValues
      (frame (values n U I.free A.Bmatrix I.nB A.Cmatrix I.nC A.Omatrix I.requesterCount A.positions A.menu A.J p R F q))
      I.free I.capacity=header (config p 0 I A 0) (q*q) 1 1 1 0 0 0 (addr I.free I.capacity 8) := by sorry
