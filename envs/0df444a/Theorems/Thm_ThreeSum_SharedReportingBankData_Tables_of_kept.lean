-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankData_Tables_of_kept
-- name    : ThreeSum.SharedReportingBankData.Tables.of_kept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:15:41.863343+00:00
-- url     : https://prove2.me/theorems/c1f8797b-e857-4335-9c00-fb03c741ccc7
-- title:
--   Tables: of kept
-- statement:
--   The Tables construction uses the of kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankData.lean#L46-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankData.lean#L46-L63

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

theorem ThreeSum.SharedReportingBankData.Tables.of_kept {h J k bound : ℕ} {μ ν : ℕ → ℤ} {D : Catalog} {hk : k ≤ J}
    {f g : Finset (Fin (J*(512*h))) → ℤ} (H : Tables μ D hk f g)
    (heq : Kept μ ν bound) (hindex : D.indexBase+count h k ≤ bound)
    (hptr : D.ptrBase+count h k ≤ bound)
    (hbox : D.boxBase+count h k*stride ((J-k)*(512*h)) D.boxCut ≤ bound) :
    Tables ν D hk f g := by sorry
