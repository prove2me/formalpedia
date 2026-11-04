-- Prove2me | Theorems.Thm_ThreeSum_LightReportingPositiveExpand_time_bound
-- name    : ThreeSum.LightReportingPositiveExpand.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:43:53.165411+00:00
-- url     : https://prove2.me/theorems/95f0fd4f-24a9-4f2b-b72e-191e7b511eac
-- title:
--   Light Reporting Positive Expand: time bound
-- statement:
--   The Light Reporting Positive Expand construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPositiveExpand.lean#L137-L146
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPositiveExpand.lean#L137-L146

import Definitions.Def_Submission_ThreeSum_LightReportingPositiveMasks
import Definitions.Def_Submission_ThreeSum_LightReportingPositiveExpand
import Theorems.Thm_ThreeSum_LightBlockChildrenIndexed_time_bound
import Theorems.Thm_ThreeSum_LightBlockChildren_time_bound
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
import Theorems.Thm_ThreeSum_LightReportingCatalogBatch_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_d9f2c07378eda243
import Theorems.Thm_ThreeSum_LightReportingCatalogLevel_time_bound
import Theorems.Thm_ThreeSum_LightReportingCatalogQuery_time_bound
import Theorems.Thm_ThreeSum_LightReportingGatherPair_time_bound
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
open ThreeSum ThreeSum.LightReportingPositiveExpand
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostMasks LightBlockChildrenIndexed ReportingHostPositive LightReportingPositiveMasks
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.LightReportingPositiveExpand.time_bound {h J k t : ℕ} (hk : k < J) (ht : t ≤ residualSize h J (k+1)+1) :
    time h J k t ≤
      26000*(width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J (k+1)) t+1)*(groupSize h+1) := by sorry
