-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffixCosts_downsetCap_le_layer
-- name    : ThreeSum.ReportingHostSuffixCosts.downsetCap_le_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:36:18.911447+00:00
-- url     : https://prove2.me/theorems/ffb0f141-cd5a-4815-bf4a-5860e4e45189
-- title:
--   Reporting Host Suffix Costs: downset Cap le layer
-- statement:
--   The Reporting Host Suffix Costs construction uses the downset Cap le layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffixCosts.lean#L17-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffixCosts.lean#L17-L26

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffixCosts
open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open scoped BigOperators

theorem ThreeSum.ReportingHostSuffixCosts.downsetCap_le_layer {V cut : ℕ} (hhalf : cut ≤ V/2) :
    downsetCap V cut ≤ (cut+1)*V.choose cut := by sorry
