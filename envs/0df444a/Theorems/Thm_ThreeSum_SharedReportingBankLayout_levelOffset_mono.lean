-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankLayout_levelOffset_mono
-- name    : ThreeSum.SharedReportingBankLayout.levelOffset_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:07:17.93578+00:00
-- url     : https://prove2.me/theorems/5935b511-8941-4852-ba7e-53fe143eb905
-- title:
--   Shared Reporting Bank Layout: level Offset mono
-- statement:
--   The Shared Reporting Bank Layout construction uses the level Offset mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLayout.lean#L140-L141
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLayout.lean#L140-L141

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLayout
open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1400000
set_option maxRecDepth 9000

theorem ThreeSum.SharedReportingBankLayout.levelOffset_mono (h J : ℕ) (boxCut : ℕ → ℕ) : Monotone (levelOffset h J boxCut) := by sorry
