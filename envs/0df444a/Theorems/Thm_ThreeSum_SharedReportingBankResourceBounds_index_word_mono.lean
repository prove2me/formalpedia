-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_index_word_mono
-- name    : ThreeSum.SharedReportingBankResourceBounds.index_word_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:19:01.542955+00:00
-- url     : https://prove2.me/theorems/bb462e54-a991-42a0-bf64-ab3dd9b010f5
-- title:
--   Shared Reporting Bank Resource Bounds: index word mono
-- statement:
--   The Shared Reporting Bank Resource Bounds construction uses the index word mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankResourceBounds.lean#L123-L127
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankResourceBounds.lean#L123-L127

import Definitions.Def_Submission_ThreeSum_SharedReportingBankCosts
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Light SubsetAddress SharedReportingBankLayout SharedReportingBankLevels
open SharedReportingBankHeader SharedReportingBankRows
set_option maxHeartbeats 2800000
set_option maxRecDepth 14000

theorem ThreeSum.SharedReportingBankResourceBounds.index_word_mono {W a b : ℕ} (hab : a ≤ b) :
    LightReportingSortedCatalog.word W a ≤ LightReportingSortedCatalog.word W b := by sorry
