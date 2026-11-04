-- Prove2me | Theorems.Thm_ThreeSum_LightReportingPrefixCatalog_readL
-- name    : ThreeSum.LightReportingPrefixCatalog.readL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:02:00.795202+00:00
-- url     : https://prove2.me/theorems/2bd2cb6f-4251-412a-b47f-1f71e7a462b8
-- title:
--   Light Reporting Prefix Catalog: read L
-- statement:
--   The Light Reporting Prefix Catalog construction uses the read L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPrefixCatalog.lean#L54-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPrefixCatalog.lean#L54-L62

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

theorem ThreeSum.LightReportingPrefixCatalog.readL {h J k a : ℕ} {μ : ℕ → ℤ} (hk : k ≤ J)
    (hs : Seg μ a (RadixKeyLists.values ((2^(512*h) : ℕ) : ℤ)
      (ReportingHostPairSegments.leftMasks (512*h) h) k)) :
    ∀ i < count h k, μ (a+i) = (subsetMask (preL h J k i) : ℤ) := by sorry
