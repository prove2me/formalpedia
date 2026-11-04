-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_records_nonempty_of_good
-- name    : ThreeSum.WeightedGlobalGoodOutputCatalog.records_nonempty_of_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:00:25.04861+00:00
-- url     : https://prove2.me/theorems/c6f11197-45ea-42bb-bfb7-b5684f5d2f48
-- title:
--   Weighted Global Good Output Catalog: records nonempty of good
-- statement:
--   The Weighted Global Good Output Catalog construction uses the records nonempty of good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGoodOutputCatalog.lean#L98-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGoodOutputCatalog.lean#L98-L102

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

theorem ThreeSum.WeightedGlobalGoodOutputCatalog.records_nonempty_of_good (maps : I → Weight m p) (τ : ℕ)
    (i : I) (hi : maps i∉rawBadMaps m p τ) (q : Output m) : (records maps τ)≠[] := by sorry
