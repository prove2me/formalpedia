-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankLevels_baseAt_zero
-- name    : ThreeSum.SharedReportingBankLevels.baseAt_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:38:43.248432+00:00
-- url     : https://prove2.me/theorems/c9d86fab-2a36-4ee4-a9ff-347e142fd92f
-- title:
--   Shared Reporting Bank Levels: base At zero
-- statement:
--   The Shared Reporting Bank Levels construction uses the base At zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLevels.lean#L82-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLevels.lean#L82-L82

import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1400000

theorem ThreeSum.SharedReportingBankLevels.baseAt_zero (base h J : ℕ) : baseAt base h J 0=base := by sorry
