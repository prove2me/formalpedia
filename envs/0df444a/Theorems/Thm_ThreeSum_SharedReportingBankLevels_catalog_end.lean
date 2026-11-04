-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankLevels_catalog_end
-- name    : ThreeSum.SharedReportingBankLevels.catalog_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:24:17.950683+00:00
-- url     : https://prove2.me/theorems/9fd32b79-4fdd-4e5f-b63e-812044670534
-- title:
--   Shared Reporting Bank Levels: catalog end
-- statement:
--   The Shared Reporting Bank Levels construction uses the catalog end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLevels.lean#L100-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLevels.lean#L100-L112

import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1400000

theorem ThreeSum.SharedReportingBankLevels.catalog_end (base h J k : ℕ) :
    (catalogAt base h J k).indexBase+count h k ≤ baseAt base h J (k+1) ∧
    (catalogAt base h J k).ptrBase+count h k ≤ baseAt base h J (k+1) ∧
    (catalogAt base h J k).boxBase+count h k*
      stride ((J-k)*(512*h)) (boxCut h J k) ≤ baseAt base h J (k+1) := by sorry
