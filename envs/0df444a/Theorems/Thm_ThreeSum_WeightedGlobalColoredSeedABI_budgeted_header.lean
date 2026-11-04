-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredSeedABI_budgeted_header
-- name    : ThreeSum.WeightedGlobalColoredSeedABI.budgeted_header
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:32:21.169111+00:00
-- url     : https://prove2.me/theorems/717e8225-2f5b-436f-a8b7-6bcfc91eb867
-- title:
--   Weighted Global Colored Seed ABI: budgeted header
-- statement:
--   The Weighted Global Colored Seed ABI construction uses the budgeted header property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSeedABI.lean#L20-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSeedABI.lean#L20-L29

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

theorem ThreeSum.WeightedGlobalColoredSeedABI.budgeted_header (C : Config) (seedCount newSpan K bDigit n nO : ℕ) :
    budgetedValues (header C seedCount 1 1 1 0 0 0 newSpan) K bDigit n C.J nO=
      header C seedCount 1 1 1 (n^2) (n^2) (LightTernaryInitialBudgets.initial K bDigit n C.J nO) newSpan := by sorry
