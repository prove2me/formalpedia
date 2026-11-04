-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_packed_emod
-- name    : ThreeSum.ReportingHostPackedCatalog.packed_emod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:04:58.453464+00:00
-- url     : https://prove2.me/theorems/b58f03d7-c947-441e-8083-7c51dd5cf345
-- title:
--   Reporting Host Packed Catalog: packed emod
-- statement:
--   The Reporting Host Packed Catalog construction uses the packed emod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPackedCatalog.lean#L46-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPackedCatalog.lean#L46-L48

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPackedCatalog
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder
set_option maxHeartbeats 600000

theorem ThreeSum.ReportingHostPackedCatalog.packed_emod {key : ℕ → ℕ} {n i : ℕ} (hi : i < n) :
    ((packed key n i : ℕ) : ℤ)%((n+1 : ℕ) : ℤ) = (i : ℤ) := by sorry
