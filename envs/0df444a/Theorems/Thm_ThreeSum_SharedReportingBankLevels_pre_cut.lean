-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankLevels_pre_cut
-- name    : ThreeSum.SharedReportingBankLevels.pre_cut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:37:44.370936+00:00
-- url     : https://prove2.me/theorems/18ed32b6-5dd3-42e7-9c2e-11967dd919bd
-- title:
--   Shared Reporting Bank Levels: pre cut
-- statement:
--   The Shared Reporting Bank Levels construction uses the pre cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLevels.lean#L56-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLevels.lean#L56-L60

import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1400000

theorem ThreeSum.SharedReportingBankLevels.pre_cut {h J k : ℕ} (hk : k ≤ J) : k*h+boxCut h J k ≤ 2*h*J := by sorry
