-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankRows_entry_of_later_block
-- name    : ThreeSum.SharedReportingBankRows.entry_of_later_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:47:11.943374+00:00
-- url     : https://prove2.me/theorems/e7ede3ad-21de-40ef-adc3-fae87b660db3
-- title:
--   Shared Reporting Bank Rows: entry of later block
-- statement:
--   The Shared Reporting Bank Rows construction uses the entry of later block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankRows.lean#L84-L98
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankRows.lean#L84-L98

import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankRows
open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankData SharedReportingBankLayout SharedReportingBankLevels
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
set_option maxHeartbeats 1800000

theorem ThreeSum.SharedReportingBankRows.entry_of_later_block {h J k record nextRecord n low bound : ℕ} {μ ν : ℕ → ℤ}
    {D : Catalog} {hk : k ≤ J} {f g : Finset (Fin (J*(512*h))) → ℤ}
    (H : Entry μ record D hk f g) (heq : KeptBut μ ν bound nextRecord n)
    (hrecord : record+5 ≤ nextRecord) (hnext : nextRecord+n ≤ low)
    (hlow : low ≤ bound) (hindexLow : low ≤ D.indexBase)
    (hptrLow : low ≤ D.ptrBase) (hboxLow : low ≤ D.boxBase)
    (hindex : D.indexBase+count h k ≤ bound) (hptr : D.ptrBase+count h k ≤ bound)
    (hbox : D.boxBase+count h k*stride ((J-k)*(512*h)) D.boxCut ≤ bound) :
    Entry ν record D hk f g := by sorry
