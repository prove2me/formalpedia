-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixOrder_preL_get
-- name    : ThreeSum.ReportingHostPrefixOrder.preL_get
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:57:03.482213+00:00
-- url     : https://prove2.me/theorems/7894c99e-dca2-4e60-b133-5c3fb5cc5c03
-- title:
--   Reporting Host Prefix Order: pre L get
-- statement:
--   The Reporting Host Prefix Order construction uses the pre L get property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixOrder.lean#L68-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixOrder.lean#L68-L71

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixOrder
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPairEnumeration
open ReportingHostPrefixMasks ReportingHostPairSegments
set_option maxHeartbeats 600000

theorem ThreeSum.ReportingHostPrefixOrder.preL_get {h J k i : ℕ} (hi : i < (prefixes h k).length) :
    preL h J k i = leftSet (J := J) (prefixes h k)[i] := by sorry
