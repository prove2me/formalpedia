-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankData_Tables_reporting
-- name    : ThreeSum.SharedReportingBankData.Tables.reporting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:02:29.227706+00:00
-- url     : https://prove2.me/theorems/82d11477-0eeb-4b6c-b197-bf062189539a
-- title:
--   Tables: reporting
-- statement:
--   The Tables construction uses the reporting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankData.lean#L76-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankData.lean#L76-L83

import Definitions.Def_Submission_ThreeSum_ReportingHostLevelData
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankData
open Light SubsetAddress ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
set_option maxHeartbeats 1500000
set_option maxRecDepth 9000

theorem ThreeSum.SharedReportingBankData.Tables.reporting {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {h J k : ℕ} {μ : ℕ → ℤ} {D : Catalog} {hk : k ≤ J}
    (p shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (q : GlobalEncoding.GlobalOutput h J)
    (H : Tables μ D hk (BlockIndexedQuery.leftSource p B b q)
      (BlockIndexedQuery.rightSource p shift C c q)) :
    ReportingHostLevelData.Stored μ D hk p shift B C b c q := by sorry
