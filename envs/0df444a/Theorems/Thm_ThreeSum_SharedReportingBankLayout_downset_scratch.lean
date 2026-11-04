-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankLayout_downset_scratch
-- name    : ThreeSum.SharedReportingBankLayout.downset_scratch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:07:20.210109+00:00
-- url     : https://prove2.me/theorems/c892eb39-d695-4884-bc44-fd1e13a2e897
-- title:
--   Shared Reporting Bank Layout: downset scratch
-- statement:
--   The Shared Reporting Bank Layout construction uses the downset scratch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLayout.lean#L100-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLayout.lean#L100-L107

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLayout
open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1400000
set_option maxRecDepth 9000

theorem ThreeSum.SharedReportingBankLayout.downset_scratch {h J k : ℕ} (hk : k ≤ J) (base boxCut : ℕ) :
    base+tableSize ((J-k)*(512*h))+((J-k)*(512*h)+1) ≤ finish base h J k boxCut := by sorry
