-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostLevelData_Bounds_mono
-- name    : ThreeSum.ReportingHostLevelData.Bounds.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:56:48.959033+00:00
-- url     : https://prove2.me/theorems/ff77c4a5-2834-4f8c-a729-ea31ced0f80a
-- title:
--   Bounds: mono
-- statement:
--   The Bounds construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostLevelData.lean#L76-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostLevelData.lean#L76-L79

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogQuery
import Definitions.Def_Submission_ThreeSum_LightReportingFrontierStep
import Definitions.Def_Submission_ThreeSum_ReportingHostLevelData
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostLevelData
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostLevelData.Bounds.mono {h J k baseL baseR stop stop' : ℕ} {D : Catalog}
    (H : Bounds h J k D baseL baseR stop) (hle : stop≤stop') :
    Bounds h J k D baseL baseR stop' := by sorry
