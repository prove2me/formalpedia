-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_cap_real_le_twice
-- name    : ThreeSum.WeightedGlobalGoodOutputCatalog.cap_real_le_twice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:07:48.297996+00:00
-- url     : https://prove2.me/theorems/43f98e2f-658e-4dcf-802f-5c374d1205b0
-- title:
--   Weighted Global Good Output Catalog: cap real le twice
-- statement:
--   The Weighted Global Good Output Catalog construction uses the cap real le twice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGoodOutputCatalog.lean#L242-L249
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGoodOutputCatalog.lean#L242-L249

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryLiteralOutputCap
import Definitions.Def_Submission_Weighted_Global_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalGoodOutputCatalog
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open WeightedGlobalCoverGoodMaps TernaryCoverFibers WeightedGlobalLocalParameters WeightedGlobalPartitionCount
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
variable {m p : ℕ} [Fact p.Prime]
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem ThreeSum.WeightedGlobalGoodOutputCatalog.cap_real_le_twice (τ : ℕ)
    (hA : Rbar m≤partitionLoss (2380004124000*m) (292746547000*m)*p*τ) :
    (cap m p τ : ℝ)≤2*(((partitionLoss (2380004124000*m) (292746547000*m)*p*τ : ℕ) : ℝ)/(Rbar m : ℝ)) := by sorry
