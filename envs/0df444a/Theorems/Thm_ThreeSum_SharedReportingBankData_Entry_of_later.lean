-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankData_Entry_of_later
-- name    : ThreeSum.SharedReportingBankData.Entry.of_later
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:13:08.338554+00:00
-- url     : https://prove2.me/theorems/f947788e-6c4d-472f-b9cc-3009144378c9
-- title:
--   Entry: of later
-- statement:
--   The Entry construction uses the of later property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankMemory.lean#L33-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankMemory.lean#L33-L47

import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankData
open Light SubsetAddress ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData

theorem ThreeSum.SharedReportingBankData.Entry.of_later {h J k record nextRecord low bound : ℕ} {μ ν : ℕ → ℤ}
    {D : Catalog} {hk : k ≤ J} {f g : Finset (Fin (J*(512*h))) → ℤ}
    (H : Entry μ record D hk f g) (heq : KeptBut μ ν bound nextRecord 5)
    (hrecord : record+5 ≤ nextRecord) (hnext : nextRecord+5 ≤ low)
    (hlow : low ≤ bound) (hindexLow : low ≤ D.indexBase)
    (hptrLow : low ≤ D.ptrBase) (hboxLow : low ≤ D.boxBase)
    (hindex : D.indexBase+count h k ≤ bound) (hptr : D.ptrBase+count h k ≤ bound)
    (hbox : D.boxBase+count h k*stride ((J-k)*(512*h)) D.boxCut ≤ bound) :
    Entry ν record D hk f g := by sorry
