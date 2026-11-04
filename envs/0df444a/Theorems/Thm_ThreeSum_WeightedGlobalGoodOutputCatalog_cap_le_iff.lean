-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_cap_le_iff
-- name    : ThreeSum.WeightedGlobalGoodOutputCatalog.cap_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:02:20.216499+00:00
-- url     : https://prove2.me/theorems/80c147b1-7637-41d3-9d9e-126ae46400b6
-- title:
--   Weighted Global Good Output Catalog: cap le iff
-- statement:
--   The Weighted Global Good Output Catalog construction uses the cap le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGoodOutputCatalog.lean#L179-L181
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGoodOutputCatalog.lean#L179-L181

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

theorem ThreeSum.WeightedGlobalGoodOutputCatalog.cap_le_iff (τ C : ℕ) : cap m p τ≤C ↔
    partitionLoss (2380004124000*m) (292746547000*m)*p*τ≤Rbar m*C := by sorry
