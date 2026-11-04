-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankSources_entry_reuse
-- name    : ThreeSum.SharedReportingBankSources.entry_reuse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:10:20.813843+00:00
-- url     : https://prove2.me/theorems/24b188f2-ebba-4d6a-9421-4c8810191212
-- title:
--   Shared Reporting Bank Sources: entry reuse
-- statement:
--   The Shared Reporting Bank Sources construction uses the entry reuse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankSources.lean#L65-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankSources.lean#L65-L72

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSources
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankSources
open Light GlobalEncoding BlockEncoding BlockIndexedQuery SharedReportingBankData
open BlockSourceOccurrenceOrder BlockSourceSharing OutputDecodeRecords

theorem ThreeSum.SharedReportingBankSources.entry_reuse {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {h J k record : ℕ} {μ : ℕ → ℤ}
    {D : ReportingHostLevelData.Catalog} {hk : k ≤ J}
    (p shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    {q q' : GlobalOutput h J} (ho : outputOccurrences q=outputOccurrences q')
    (H : Entry μ record D hk (leftSource p B b q) (rightSource p shift C c q)) :
    Entry μ record D hk (leftSource p B b q') (rightSource p shift C c q') := by sorry
