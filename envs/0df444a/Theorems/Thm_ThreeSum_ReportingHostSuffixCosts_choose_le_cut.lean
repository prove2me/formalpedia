-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffixCosts_choose_le_cut
-- name    : ThreeSum.ReportingHostSuffixCosts.choose_le_cut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:36:22.38721+00:00
-- url     : https://prove2.me/theorems/088cfee1-0835-4568-a8a1-e73faad9f3b4
-- title:
--   Reporting Host Suffix Costs: choose le cut
-- statement:
--   The Reporting Host Suffix Costs construction uses the choose le cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffixCosts.lean#L10-L15
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffixCosts.lean#L10-L15

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffixCosts
open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open scoped BigOperators

theorem ThreeSum.ReportingHostSuffixCosts.choose_le_cut {V j cut : ℕ} (hj : j ≤ cut) (hhalf : cut ≤ V/2) :
    V.choose j ≤ V.choose cut := by sorry
