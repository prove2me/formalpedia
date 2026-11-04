-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostCatalogSelection_original_index
-- name    : ThreeSum.ReportingHostCatalogSelection.original_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:20:18.451642+00:00
-- url     : https://prove2.me/theorems/13e84dde-16d6-427d-b466-53fc260f302f
-- title:
--   Reporting Host Catalog Selection: original index
-- statement:
--   The Reporting Host Catalog Selection construction uses the original index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogSelection.lean#L20-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogSelection.lean#L20-L28

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixQueryIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogSelection
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogSelection
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixCatalog ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog

theorem ThreeSum.ReportingHostCatalogSelection.original_index {h J k : ℕ} (hk : k ≤ J) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) :
    ∃ i < count h k,
      preL h J k i = leftPrefix k (prefixRows (J := J) pre) ∧
      preR h J k i = rightPrefix k (outputRows q) (prefixRows (J := J) pre) := by sorry
