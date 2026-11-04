-- Prove2me | Theorems.Thm_ThreeSum_LightReportingCatalogBatch_time_bound
-- name    : ThreeSum.LightReportingCatalogBatch.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:57:30.906471+00:00
-- url     : https://prove2.me/theorems/8f80c265-1bc4-47b3-b0d0-637f01468d2d
-- title:
--   Light Reporting Catalog Batch: time bound
-- statement:
--   The Light Reporting Catalog Batch construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingCatalogBatch.lean#L187-L194
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingCatalogBatch.lean#L187-L194

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogQuery
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixValueBounds
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogBatch
import Definitions.Def_WeightedCache3SUM_Alias_395153661a990775
import Theorems.Thm_ThreeSum_LightBoxSum_time_bound
import Theorems.Thm_ThreeSum_LightCanonicalBoxSum_time_bound
import Theorems.Thm_ThreeSum_LightDownsetAddress_time_bound
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightExplicitSum_time_bound
import Theorems.Thm_ThreeSum_LightLeafSum_time_bound
import Theorems.Thm_ThreeSum_LightMaskMinimum_time_bound
import Theorems.Thm_ThreeSum_LightMaskUnion_time_bound
import Theorems.Thm_ThreeSum_LightQueryBox_time_bound
import Theorems.Thm_ThreeSum_LightQueryEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightQueryWeights_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_a98211a6e8223f5f
import Theorems.Thm_ThreeSum_LightRadixRows_time_bound
import Theorems.Thm_ThreeSum_LightReportingCatalogQuery_time_bound
import Theorems.Thm_ThreeSum_LightReportingPairRows_time_bound
import Theorems.Thm_ThreeSum_LightReportingPrefixArrays_time_bound
import Theorems.Thm_ThreeSum_LightReportingSortedCatalog_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixBatch_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_aee3f2a8e7e7d37a
import Theorems.Thm_ThreeSum_LightReportingSuffixCatalog_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixCell_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixExplicit_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixLower_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixQueryHost_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixQueryIndexed_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_d5b1b0bdde74f397
import Theorems.Thm_ThreeSum_LightReportingSuffixSetup_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixSum_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_306830be6786141e
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafCell_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafTable_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeaf_time_bound
import Theorems.Thm_ThreeSum_LightSparseQuery_time_bound
import Theorems.Thm_ThreeSum_LightStageLookup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Definitions.Def_WeightedCache3SUM_Alias_c2a1891cab57c5b2

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingCatalogBatch
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.LightReportingCatalogBatch.time_bound {h J k t n : ℕ} (hk : k ≤ J) (ht : t ≤ residualSize h J k+1) :
    time h J k t n ≤
      21000*(width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1)*(n+1) := by sorry
