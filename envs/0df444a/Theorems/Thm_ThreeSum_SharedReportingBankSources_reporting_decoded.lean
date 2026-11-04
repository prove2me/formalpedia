-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankSources_reporting_decoded
-- name    : ThreeSum.SharedReportingBankSources.reporting_decoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:11:16.865974+00:00
-- url     : https://prove2.me/theorems/24955485-fa74-40c2-bccf-4ff13118b950
-- title:
--   Shared Reporting Bank Sources: reporting decoded
-- statement:
--   The Shared Reporting Bank Sources construction uses the reporting decoded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankSources.lean#L74-L86
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankSources.lean#L74-L86

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSources
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankSources
open Light GlobalEncoding BlockEncoding BlockIndexedQuery SharedReportingBankData
open BlockSourceOccurrenceOrder BlockSourceSharing OutputDecodeRecords

theorem ThreeSum.SharedReportingBankSources.reporting_decoded {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {h J k output record : ℕ} {μ : ℕ → ℤ}
    {D : ReportingHostLevelData.Catalog} {hk : k ≤ J}
    (p shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (houtput : output < localCount h^J)
    (H : Entry μ record D hk
      (leftSource p B b (representative h J
        (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output)))
      (rightSource p shift C c (representative h J
        (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output)))) :
    ReportingHostLevelData.Stored μ D hk p shift B C b c
      ((GlobalKeyEnumeration.globalRecords h J).getD output (outputDefault h J)) := by sorry
