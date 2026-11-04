-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_native_fiber_cap
-- name    : ThreeSum.WeightedGlobalGoodOutputCatalog.native_fiber_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:07:18.616023+00:00
-- url     : https://prove2.me/theorems/6c92c062-90cb-4743-84b7-988ff10662cc
-- title:
--   Weighted Global Good Output Catalog: native fiber cap
-- statement:
--   The Weighted Global Good Output Catalog construction uses the native fiber cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGoodOutputCatalog.lean#L61-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGoodOutputCatalog.lean#L61-L67

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

theorem ThreeSum.WeightedGlobalGoodOutputCatalog.native_fiber_cap (τ : ℕ) (w : Weight m p) (hgood : w∉rawBadMaps m p τ) (o : ZMod p) :
    outputFiberCount (native w) o≤cap m p τ := by sorry
