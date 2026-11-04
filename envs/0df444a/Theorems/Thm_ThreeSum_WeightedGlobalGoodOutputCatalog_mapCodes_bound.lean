-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_mapCodes_bound
-- name    : ThreeSum.WeightedGlobalGoodOutputCatalog.mapCodes_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:07:37.110565+00:00
-- url     : https://prove2.me/theorems/a49b1766-eef8-4eff-ad8c-503448e79b4f
-- title:
--   Weighted Global Good Output Catalog: map Codes bound
-- statement:
--   The Weighted Global Good Output Catalog construction uses the map Codes bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGoodOutputCatalog.lean#L207-L213
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGoodOutputCatalog.lean#L207-L213

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

theorem ThreeSum.WeightedGlobalGoodOutputCatalog.mapCodes_bound {F : ℕ} (maps : Fin F → Weight m p) (τ : ℕ) :
    ∀i<(raws maps τ).length, (mapCodes maps τ).getD i 0<F := by sorry
