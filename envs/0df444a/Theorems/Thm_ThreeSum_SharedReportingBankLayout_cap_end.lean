-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankLayout_cap_end
-- name    : ThreeSum.SharedReportingBankLayout.cap_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:07:58.749415+00:00
-- url     : https://prove2.me/theorems/16cd1339-8942-4424-85fe-707cb20874c5
-- title:
--   Shared Reporting Bank Layout: cap end
-- statement:
--   The Shared Reporting Bank Layout construction uses the cap end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLayout.lean#L79-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLayout.lean#L79-L82

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLayout
open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1400000
set_option maxRecDepth 9000

theorem ThreeSum.SharedReportingBankLayout.cap_end (base h J k boxCut : ℕ) :
    masks base h J k boxCut+cap h J k boxCut ≤ work base h J k boxCut := by sorry
