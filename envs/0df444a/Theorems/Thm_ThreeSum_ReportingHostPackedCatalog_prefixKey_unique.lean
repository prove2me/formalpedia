-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_prefixKey_unique
-- name    : ThreeSum.ReportingHostPackedCatalog.prefixKey_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:07:47.884382+00:00
-- url     : https://prove2.me/theorems/e240fe3c-f7dd-4205-8e4d-3c578ecaef7f
-- title:
--   Reporting Host Packed Catalog: prefix Key unique
-- statement:
--   The Reporting Host Packed Catalog construction uses the prefix Key unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPackedCatalog.lean#L127-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPackedCatalog.lean#L127-L135

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPackedCatalog
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder
set_option maxHeartbeats 600000

theorem ThreeSum.ReportingHostPackedCatalog.prefixKey_unique {h J k : ℕ} (hk : k ≤ J) :
    ∀ i < LightReportingPrefixCatalog.count h k,
    ∀ j < LightReportingPrefixCatalog.count h k,
      prefixKey h J k i=prefixKey h J k j → i=j := by sorry
