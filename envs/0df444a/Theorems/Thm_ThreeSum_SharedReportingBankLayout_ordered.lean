-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankLayout_ordered
-- name    : ThreeSum.SharedReportingBankLayout.ordered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:10:08.631172+00:00
-- url     : https://prove2.me/theorems/aab77e3c-0cc7-4f8e-87ae-f70deb39f9b9
-- title:
--   Shared Reporting Bank Layout: ordered
-- statement:
--   The Shared Reporting Bank Layout construction uses the ordered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLayout.lean#L55-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLayout.lean#L55-L62

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLayout
open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1400000
set_option maxRecDepth 9000

theorem ThreeSum.SharedReportingBankLayout.ordered (base h J k boxCut : ℕ) :
    base ≤ pairL base h ∧ pairL base h ≤ pairR base h ∧ pairR base h ≤ stageL base h ∧
      stageL base h ≤ stageR base h k ∧ stageR base h k ≤ pointers base h k ∧
      pointers base h k ≤ boxes base h k ∧ boxes base h k ≤ masks base h J k boxCut ∧
      masks base h J k boxCut ≤ work base h J k boxCut ∧
      work base h J k boxCut ≤ finish base h J k boxCut := by sorry
