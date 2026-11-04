-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankData_Entry_of_kept
-- name    : ThreeSum.SharedReportingBankData.Entry.of_kept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:15:33.534294+00:00
-- url     : https://prove2.me/theorems/bbd2dccc-5790-482c-a29f-dc22b1ff5019
-- title:
--   Entry: of kept
-- statement:
--   The Entry construction uses the of kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankData.lean#L65-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankData.lean#L65-L74

import Definitions.Def_Submission_ThreeSum_ReportingHostLevelData
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Theorems.Thm_ThreeSum_ReportingHostLevelData_Sources_of_kept
import Definitions.Def_WeightedCache3SUM_Alias_ed168a32962ea724

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankData
open Light SubsetAddress ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
set_option maxHeartbeats 1500000
set_option maxRecDepth 9000

theorem ThreeSum.SharedReportingBankData.Entry.of_kept {h J k record bound : ℕ} {μ ν : ℕ → ℤ} {D : Catalog} {hk : k ≤ J}
    {f g : Finset (Fin (J*(512*h))) → ℤ} (H : Entry μ record D hk f g)
    (heq : Kept μ ν bound) (hrecord : record+5 ≤ bound)
    (hindex : D.indexBase+count h k ≤ bound) (hptr : D.ptrBase+count h k ≤ bound)
    (hbox : D.boxBase+count h k*stride ((J-k)*(512*h)) D.boxCut ≤ bound) :
    Entry ν record D hk f g := by sorry
