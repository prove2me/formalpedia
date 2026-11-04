-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_fixed_output_cap
-- name    : ThreeSum.WeightedGlobalGoodOutputCatalog.fixed_output_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:07:17.63666+00:00
-- url     : https://prove2.me/theorems/96352030-6a4b-4104-ab57-7d9767d963c0
-- title:
--   Weighted Global Good Output Catalog: fixed output cap
-- statement:
--   The Weighted Global Good Output Catalog construction uses the fixed output cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGoodOutputCatalog.lean#L36-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGoodOutputCatalog.lean#L36-L59

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

theorem ThreeSum.WeightedGlobalGoodOutputCatalog.fixed_output_cap (τ : ℕ) (w : Weight m p)
    (hgood : w∉rawBadMaps m p τ) (o : ZMod p) :
    Rbar m*outputFiberCount (native w) o≤partitionLoss (2380004124000*m) (292746547000*m)*p*τ := by sorry
