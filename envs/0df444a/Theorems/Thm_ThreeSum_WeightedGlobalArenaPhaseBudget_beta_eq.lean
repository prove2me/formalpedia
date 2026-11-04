-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_beta_eq
-- name    : ThreeSum.WeightedGlobalArenaPhaseBudget.beta_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T01:03:52.901415+00:00
-- url     : https://prove2.me/theorems/c340c07a-0419-474f-9b4c-8e22e4297bc8
-- title:
--   Weighted Global Arena Phase Budget: beta eq
-- statement:
--   The Weighted Global Arena Phase Budget construction uses the beta eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPhaseBudget.lean#L138-L141
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPhaseBudget.lean#L138-L141

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

theorem ThreeSum.WeightedGlobalArenaPhaseBudget.beta_eq (m F K : ℕ) :
    9*pairFactor m F K=9*F*(WeightedGlobalCoverScale.outputSize m)*(WeightedGlobalGoodOutputCatalog.Rbar m)^K := by sorry
