-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankLevels_residual_le_width
-- name    : ThreeSum.SharedReportingBankLevels.residual_le_width
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:36:56.423579+00:00
-- url     : https://prove2.me/theorems/abee08c4-6c9a-415e-a103-45518a8fc307
-- title:
--   Shared Reporting Bank Levels: residual le width
-- statement:
--   The Shared Reporting Bank Levels construction uses the residual le width property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLevels.lean#L52-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLevels.lean#L52-L54

import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1400000

theorem ThreeSum.SharedReportingBankLevels.residual_le_width (h J k : ℕ) : residual h J k ≤ (J-k)*(512*h) := by sorry
