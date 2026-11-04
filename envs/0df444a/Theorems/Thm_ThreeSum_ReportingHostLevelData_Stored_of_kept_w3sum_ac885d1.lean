-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostLevelData_Stored_of_kept_w3sum_ac885d1
-- name    : ThreeSum.ReportingHostLevelData.Stored.of_kept_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:57:58.244519+00:00
-- url     : https://prove2.me/theorems/873b243f-43b2-488f-b47d-f7dfeab4716e
-- title:
--   Stored: of kept
-- statement:
--   The Stored construction uses the of kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostLevelData.lean#L91-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostLevelData.lean#L91-L107

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogQuery
import Definitions.Def_Submission_ThreeSum_LightReportingFrontierStep
import Definitions.Def_Submission_ThreeSum_ReportingHostLevelData
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

theorem ThreeSum.ReportingHostLevelData.Stored.of_kept_w3sum_ac885d1 {h J k baseL baseR stop : ℕ} {μ ν : ℕ→ℤ} {D : Catalog} {hk : k≤J}
    {pMod shift : ℤ} {B : Finset β} {C : Finset γ} {b : β→ℤ} {c : γ→ℤ} {q : GlobalOutput h J}
    (H : Stored μ D hk pMod shift B C b c q) (HB : Bounds h J k D baseL baseR stop)
    (hkeep : Kept μ ν stop) : Stored ν D hk pMod shift B C b c q := by sorry
