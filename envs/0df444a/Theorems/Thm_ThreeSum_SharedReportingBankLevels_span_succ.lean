-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankLevels_span_succ
-- name    : ThreeSum.SharedReportingBankLevels.span_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:27:18.229209+00:00
-- url     : https://prove2.me/theorems/961b638d-fb9b-450f-9d64-5c0704322d7d
-- title:
--   Shared Reporting Bank Levels: span succ
-- statement:
--   The Shared Reporting Bank Levels construction uses the span succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLevels.lean#L67-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLevels.lean#L67-L71

import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1400000

theorem ThreeSum.SharedReportingBankLevels.span_succ (h k : ℕ) : prefixSpan h (k+1)=prefixSpan h k+1+count h (k+1) := by sorry
