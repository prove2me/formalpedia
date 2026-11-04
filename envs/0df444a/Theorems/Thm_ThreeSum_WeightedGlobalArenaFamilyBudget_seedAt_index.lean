-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFamilyBudget_seedAt_index
-- name    : ThreeSum.WeightedGlobalArenaFamilyBudget.seedAt_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:32:13.347065+00:00
-- url     : https://prove2.me/theorems/991927df-bcb7-42bf-8f53-c86c4fc55c89
-- title:
--   Weighted Global Arena Family Budget: seed At index
-- statement:
--   The Weighted Global Arena Family Budget construction uses the seed At index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFamilyBudget.lean#L23-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFamilyBudget.lean#L23-L24

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaBudgetExistence
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFamilyBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFamilyBudget
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory
open LightWeightedGlobalControllerFactory TernaryOriginalRowMenu TernaryExtensionEncoding
open WeightedGlobalArenaSeedData WeightedGlobalArenaBudgetExistence
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem ThreeSum.WeightedGlobalArenaFamilyBudget.seedAt_index (e : (E×E)≃Fin N) (seed : E×E) : seedAt e (e seed).val=seed := by sorry
