-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_packed_interval_unique
-- name    : ThreeSum.ReportingHostPackedCatalog.packed_interval_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:07:22.323573+00:00
-- url     : https://prove2.me/theorems/0e0a1115-e461-44bf-a3cf-edfd009b41ed
-- title:
--   Reporting Host Packed Catalog: packed interval unique
-- statement:
--   The Reporting Host Packed Catalog construction uses the packed interval unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPackedCatalog.lean#L50-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPackedCatalog.lean#L50-L65

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPackedCatalog
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder
set_option maxHeartbeats 600000

theorem ThreeSum.ReportingHostPackedCatalog.packed_interval_unique {key : ℕ → ℕ} {n i j : ℕ}
    (hi : i < n) (hj : j < n)
    (hunique : ∀ a < n, ∀ b < n, key a=key b → a=b)
    (hlo : packed key n i ≤ packed key n j)
    (hhi : packed key n j ≤ key i*(n+1)+n) : i=j := by sorry
