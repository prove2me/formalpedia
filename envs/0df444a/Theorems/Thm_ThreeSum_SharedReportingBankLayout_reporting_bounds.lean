-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankLayout_reporting_bounds
-- name    : ThreeSum.SharedReportingBankLayout.reporting_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:08:00.125989+00:00
-- url     : https://prove2.me/theorems/af2623c6-2b57-4dc6-9937-b97afd764459
-- title:
--   Shared Reporting Bank Layout: reporting bounds
-- statement:
--   The Shared Reporting Bank Layout construction uses the reporting bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLayout.lean#L109-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLayout.lean#L109-L129

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLayout
open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1400000
set_option maxRecDepth 9000

theorem ThreeSum.SharedReportingBankLayout.reporting_bounds {h J k base baseL baseR cut stop : ℕ}
    (t boxCut : ℕ)
    (hleft : baseL+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ base)
    (hright : baseR+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ base)
    (hcut : cut=LightBlockQuery.sourceCut h J)
    (hstop : finish base h J k boxCut ≤ stop) :
    ReportingHostLevelData.Bounds h J k (catalog base h J k boxCut t) baseL baseR stop := by sorry
