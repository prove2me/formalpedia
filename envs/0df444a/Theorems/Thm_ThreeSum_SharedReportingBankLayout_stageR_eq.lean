-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankLayout_stageR_eq
-- name    : ThreeSum.SharedReportingBankLayout.stageR_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:07:34.736011+00:00
-- url     : https://prove2.me/theorems/cb4983b5-c42f-4eee-85d7-6ee73c3b800a
-- title:
--   Shared Reporting Bank Layout: stage R eq
-- statement:
--   The Shared Reporting Bank Layout construction uses the stage R eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLayout.lean#L45-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLayout.lean#L45-L48

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLayout
open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1400000
set_option maxRecDepth 9000

theorem ThreeSum.SharedReportingBankLayout.stageR_eq (base h k : ℕ) :
    stageR base h k=LightRadixKeys.space (stageL base h) (localPairs h) k := by sorry
