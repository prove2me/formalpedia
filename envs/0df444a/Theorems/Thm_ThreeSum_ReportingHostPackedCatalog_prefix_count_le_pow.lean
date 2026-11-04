-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_prefix_count_le_pow
-- name    : ThreeSum.ReportingHostPackedCatalog.prefix_count_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:04:30.33401+00:00
-- url     : https://prove2.me/theorems/5d6d4bdc-8a77-462a-abfd-76f3319531ff
-- title:
--   Reporting Host Packed Catalog: prefix count le pow
-- statement:
--   The Reporting Host Packed Catalog construction uses the prefix count le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPackedCatalog.lean#L137-L148
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPackedCatalog.lean#L137-L148

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPackedCatalog
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder
set_option maxHeartbeats 600000

theorem ThreeSum.ReportingHostPackedCatalog.prefix_count_le_pow {h J k : ℕ} (hk : k ≤ J) :
    LightReportingPrefixCatalog.count h k ≤ 2^(2*(J*(512*h))) := by sorry
