-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankLevels_finish_baseAt
-- name    : ThreeSum.SharedReportingBankLevels.finish_baseAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:27:14.650093+00:00
-- url     : https://prove2.me/theorems/45b32225-2ed4-4cc8-98a4-4a3af99bb64b
-- title:
--   Shared Reporting Bank Levels: finish base At
-- statement:
--   The Shared Reporting Bank Levels construction uses the finish base At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLevels.lean#L87-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLevels.lean#L87-L89

import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1400000

theorem ThreeSum.SharedReportingBankLevels.finish_baseAt (base h J k : ℕ) :
    finish (baseAt base h J k) h J k (boxCut h J k)=baseAt base h J (k+1) := by sorry
