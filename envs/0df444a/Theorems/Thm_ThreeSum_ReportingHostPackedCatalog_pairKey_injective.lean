-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_pairKey_injective
-- name    : ThreeSum.ReportingHostPackedCatalog.pairKey_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:04:34.271398+00:00
-- url     : https://prove2.me/theorems/8712098a-7244-49ed-bbf9-d1cb1327efc4
-- title:
--   Reporting Host Packed Catalog: pair Key injective
-- statement:
--   The Reporting Host Packed Catalog construction uses the pair Key injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPackedCatalog.lean#L31-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPackedCatalog.lean#L31-L38

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPackedCatalog
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder
set_option maxHeartbeats 600000

theorem ThreeSum.ReportingHostPackedCatalog.pairKey_injective {radix l r l' r' : ℕ} (hl : l < radix) (hl' : l' < radix)
    (he : pairKey radix l r = pairKey radix l' r') : l=l' ∧ r=r' := by sorry
