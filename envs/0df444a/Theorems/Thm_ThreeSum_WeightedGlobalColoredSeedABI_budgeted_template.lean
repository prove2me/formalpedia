-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredSeedABI_budgeted_template
-- name    : ThreeSum.WeightedGlobalColoredSeedABI.budgeted_template
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:33:09.750897+00:00
-- url     : https://prove2.me/theorems/38e04edb-b4e3-4d6d-b41f-d3a0d234a5f2
-- title:
--   Weighted Global Colored Seed ABI: budgeted template
-- statement:
--   This is the exact forty-eight-cell seed list produced by the literal
--   colored initialization chunk and consumed by entry237.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSeedABI.lean#L43-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSeedABI.lean#L43-L51

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

theorem ThreeSum.WeightedGlobalColoredSeedABI.budgeted_template (I : Input) (A : Inputs) (p n U R F q K bDigit : ℕ)
    (hleft : A.leftTagged=A.Bmatrix) (hright : A.rightTagged=A.Cmatrix) :
    budgetedValues (LightWeightedGlobalArenaTemplate.seedValues
      (frame (values n U I.free A.Bmatrix I.nB A.Cmatrix I.nC A.Omatrix I.requesterCount A.positions A.menu A.J p R F q))
      I.free I.capacity) K bDigit n A.J I.requesterCount=
      header (config p 0 I A 0) (q*q) 1 1 1 (n^2) (n^2)
        (LightTernaryInitialBudgets.initial K bDigit n A.J I.requesterCount) (addr I.free I.capacity 8) := by sorry
