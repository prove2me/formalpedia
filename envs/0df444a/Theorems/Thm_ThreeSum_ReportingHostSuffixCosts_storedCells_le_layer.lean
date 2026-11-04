-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffixCosts_storedCells_le_layer
-- name    : ThreeSum.ReportingHostSuffixCosts.storedCells_le_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:36:46.559618+00:00
-- url     : https://prove2.me/theorems/5a985206-86a3-4519-a5f3-d98a13b0e36b
-- title:
--   Reporting Host Suffix Costs: stored Cells le layer
-- statement:
--   The Reporting Host Suffix Costs construction uses the stored Cells le layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffixCosts.lean#L36-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffixCosts.lean#L36-L39

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffixCosts
open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open scoped BigOperators

theorem ThreeSum.ReportingHostSuffixCosts.storedCells_le_layer {V cut : ℕ} (hhalf : cut ≤ V/2) :
    (V+1)*downsetCap V cut ≤ (V+1)*(cut+1)*V.choose cut := by sorry
