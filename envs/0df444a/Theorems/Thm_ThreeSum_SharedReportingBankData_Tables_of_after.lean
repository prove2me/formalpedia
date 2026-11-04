-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankData_Tables_of_after
-- name    : ThreeSum.SharedReportingBankData.Tables.of_after
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:02:22.493978+00:00
-- url     : https://prove2.me/theorems/2920ebe7-26c9-49db-b6c9-343fcf3717a8
-- title:
--   Tables: of after
-- statement:
--   The Tables construction uses the of after property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankData.lean#L31-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankData.lean#L31-L44

import Definitions.Def_Submission_ThreeSum_ReportingHostLevelData
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankData
open Light SubsetAddress ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
set_option maxHeartbeats 1500000
set_option maxRecDepth 9000

theorem ThreeSum.SharedReportingBankData.Tables.of_after {h J k low : ℕ} {μ ν : ℕ → ℤ} {D : Catalog} {hk : k ≤ J}
    {f g : Finset (Fin (J*(512*h))) → ℤ} (H : Tables μ D hk f g)
    (heq : ∀ a, low ≤ a → ν a=μ a)
    (hindex : low ≤ D.indexBase) (hptr : low ≤ D.ptrBase) (hbox : low ≤ D.boxBase) :
    Tables ν D hk f g := by sorry
