-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
-- name    : ThreeSum.WeightedGlobalArenaPhaseBudget.threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T01:10:36.596895+00:00
-- url     : https://prove2.me/theorems/9abdbc8a-814e-4055-a75b-165b83b79d39
-- title:
--   Weighted Global Arena Phase Budget: threshold
-- statement:
--   The Weighted Global Arena Phase Budget construction uses the threshold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPhaseBudget.lean#L23-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPhaseBudget.lean#L23-L32

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhase
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhaseBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPhaseBudget
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSeedData WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters TernaryExtensionEncoding
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem ThreeSum.WeightedGlobalArenaPhaseBudget.threshold (m j K F U0 : ℕ) :
    U0*((9*pairFactor m F K)*(2^((fixedPi m 2)*K)))^(j+1)=
      scale m j K*(9*pairFactor m F K)^(j+1)*U0 := by sorry
