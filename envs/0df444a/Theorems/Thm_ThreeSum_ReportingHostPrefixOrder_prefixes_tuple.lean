-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixOrder_prefixes_tuple
-- name    : ThreeSum.ReportingHostPrefixOrder.prefixes_tuple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:56:40.750744+00:00
-- url     : https://prove2.me/theorems/52cd1017-d3ac-42ae-85ee-24d6b33acd14
-- title:
--   Reporting Host Prefix Order: prefixes tuple
-- statement:
--   The Reporting Host Prefix Order construction uses the prefixes tuple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixOrder.lean#L29-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixOrder.lean#L29-L33

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixOrder
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPairEnumeration
open ReportingHostPrefixMasks ReportingHostPairSegments
set_option maxHeartbeats 600000

theorem ThreeSum.ReportingHostPrefixOrder.prefixes_tuple (h k : ℕ) :
    (prefixes h k).map tuple = RadixKeyLists.tuples (pairs (512*h) h) k := by sorry
