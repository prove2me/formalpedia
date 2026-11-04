-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankData_Tables_of_window_w3sum_ac885d1
-- name    : ThreeSum.SharedReportingBankData.Tables.of_window_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:12:04.380058+00:00
-- url     : https://prove2.me/theorems/d593228b-1442-4437-8707-565636dc996a
-- title:
--   Tables: of window
-- statement:
--   The Tables construction uses the of window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankMemory.lean#L10-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankMemory.lean#L10-L31

import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankData
open Light SubsetAddress ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData

theorem ThreeSum.SharedReportingBankData.Tables.of_window_w3sum_ac885d1 {h J k low bound : ℕ} {μ ν : ℕ → ℤ}
    {D : Catalog} {hk : k ≤ J} {f g : Finset (Fin (J*(512*h))) → ℤ}
    (H : Tables μ D hk f g) (heq : ∀ a, low ≤ a → a < bound → ν a=μ a)
    (hindexLow : low ≤ D.indexBase) (hptrLow : low ≤ D.ptrBase)
    (hboxLow : low ≤ D.boxBase) (hindex : D.indexBase+count h k ≤ bound)
    (hptr : D.ptrBase+count h k ≤ bound)
    (hbox : D.boxBase+count h k*stride ((J-k)*(512*h)) D.boxCut ≤ bound) :
    Tables ν D hk f g := by sorry
