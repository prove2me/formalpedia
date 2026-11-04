-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffixCosts_downsetCap_add_one_le_layer
-- name    : ThreeSum.ReportingHostSuffixCosts.downsetCap_add_one_le_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:36:13.46897+00:00
-- url     : https://prove2.me/theorems/4df79f02-c514-4bb9-9e85-d92ad9a692dc
-- title:
--   Reporting Host Suffix Costs: downset Cap add one le layer
-- statement:
--   The Reporting Host Suffix Costs construction uses the downset Cap add one le layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffixCosts.lean#L28-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffixCosts.lean#L28-L34

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffixCosts
open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open scoped BigOperators

theorem ThreeSum.ReportingHostSuffixCosts.downsetCap_add_one_le_layer {V cut : ℕ} (hhalf : cut ≤ V/2) :
    downsetCap V cut+1 ≤ (V+2)*V.choose cut := by sorry
