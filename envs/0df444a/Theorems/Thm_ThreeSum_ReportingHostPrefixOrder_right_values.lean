-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixOrder_right_values
-- name    : ThreeSum.ReportingHostPrefixOrder.right_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:01:20.086919+00:00
-- url     : https://prove2.me/theorems/c059b839-7af6-4a93-9e1e-94498808428c
-- title:
--   Reporting Host Prefix Order: right values
-- statement:
--   The Reporting Host Prefix Order construction uses the right values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixOrder.lean#L62-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixOrder.lean#L62-L66

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixOrder
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPairEnumeration
open ReportingHostPrefixMasks ReportingHostPairSegments
set_option maxHeartbeats 600000

theorem ThreeSum.ReportingHostPrefixOrder.right_values {h J k : ℕ} (hk : k ≤ J) :
    RadixKeyLists.values ((2^(512*h) : ℕ) : ℤ) (rightMasks (512*h) h) k =
      (rightSets h J k).map (fun S => (subsetMask S : ℤ)) := by sorry
