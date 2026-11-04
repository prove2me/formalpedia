-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_localBucket_cap
-- name    : ThreeSum.WeightedGlobalGoodOutputCatalog.localBucket_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:51:09.034593+00:00
-- url     : https://prove2.me/theorems/62ae4c0a-e300-44b1-b649-08e7ad9f2f70
-- title:
--   Weighted Global Good Output Catalog: local Bucket cap
-- statement:
--   The Weighted Global Good Output Catalog construction uses the local Bucket cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGoodOutputCatalog.lean#L150-L171
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGoodOutputCatalog.lean#L150-L171

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

theorem ThreeSum.WeightedGlobalGoodOutputCatalog.localBucket_cap (maps : I → Weight m p) (τ : ℕ) (x : ℤ) :
    (TernaryWantedRadix.localBucket (p : ℤ) (raws maps τ) x).length≤Fintype.card I*cap m p τ := by sorry
