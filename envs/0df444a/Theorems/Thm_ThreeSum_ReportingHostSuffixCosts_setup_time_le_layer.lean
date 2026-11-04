-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffixCosts_setup_time_le_layer
-- name    : ThreeSum.ReportingHostSuffixCosts.setup_time_le_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:36:39.325148+00:00
-- url     : https://prove2.me/theorems/281e381b-d00d-4180-b156-f4cfe0f13456
-- title:
--   Reporting Host Suffix Costs: setup time le layer
-- statement:
--   The Reporting Host Suffix Costs construction uses the setup time le layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffixCosts.lean#L41-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffixCosts.lean#L41-L54

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffixCosts
open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open scoped BigOperators

theorem ThreeSum.ReportingHostSuffixCosts.setup_time_le_layer {W V offset cut : ℕ} (hfit : offset+V ≤ W)
    (hhalf : cut ≤ V/2) :
    LightReportingSuffixSetup.time W V cut offset ≤ 40000*(W+1)^5*V.choose cut := by sorry
