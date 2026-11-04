-- Prove2me | Theorems.Thm_ThreeSum_LightReportingPrefixCatalog_readR
-- name    : ThreeSum.LightReportingPrefixCatalog.readR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:01:30.718209+00:00
-- url     : https://prove2.me/theorems/46593a19-de9e-4f32-b18a-720578218530
-- title:
--   Light Reporting Prefix Catalog: read R
-- statement:
--   The Light Reporting Prefix Catalog construction uses the read R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPrefixCatalog.lean#L64-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPrefixCatalog.lean#L64-L72

import Definitions.Def_Submission_ThreeSum_LightReportingPrefixArrays
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCatalogSetup
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingPrefixCatalog
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPrefixCatalog ReportingHostPrefixOrder ReportingHostSuffix
open LightReportingSuffixCatalog
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits}

theorem ThreeSum.LightReportingPrefixCatalog.readR {h J k a : ℕ} {μ : ℕ → ℤ} (hk : k ≤ J)
    (hs : Seg μ a (RadixKeyLists.values ((2^(512*h) : ℕ) : ℤ)
      (ReportingHostPairSegments.rightMasks (512*h) h) k)) :
    ∀ i < count h k, μ (a+i) = (subsetMask (preR h J k i) : ℤ) := by sorry
