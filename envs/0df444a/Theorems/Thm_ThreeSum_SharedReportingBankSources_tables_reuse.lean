-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankSources_tables_reuse
-- name    : ThreeSum.SharedReportingBankSources.tables_reuse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:10:23.759219+00:00
-- url     : https://prove2.me/theorems/40c13090-2327-40b3-afb8-c9082a1bf979
-- title:
--   Shared Reporting Bank Sources: tables reuse
-- statement:
--   The Shared Reporting Bank Sources construction uses the tables reuse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankSources.lean#L54-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankSources.lean#L54-L63

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSources
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankSources
open Light GlobalEncoding BlockEncoding BlockIndexedQuery SharedReportingBankData
open BlockSourceOccurrenceOrder BlockSourceSharing OutputDecodeRecords

theorem ThreeSum.SharedReportingBankSources.tables_reuse {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {h J k : ℕ} {μ : ℕ → ℤ}
    {D : ReportingHostLevelData.Catalog} {hk : k ≤ J}
    (p shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    {q q' : GlobalOutput h J} (ho : outputOccurrences q=outputOccurrences q')
    (H : Tables μ D hk (leftSource p B b q) (rightSource p shift C c q)) :
    Tables μ D hk (leftSource p B b q') (rightSource p shift C c q') := by sorry
