-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixOrder_left_values
-- name    : ThreeSum.ReportingHostPrefixOrder.left_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:57:27.138393+00:00
-- url     : https://prove2.me/theorems/f831de9c-4e9d-478d-9dc1-4c7eaa135527
-- title:
--   Reporting Host Prefix Order: left values
-- statement:
--   The Reporting Host Prefix Order construction uses the left values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixOrder.lean#L56-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixOrder.lean#L56-L60

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixOrder
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPairEnumeration
open ReportingHostPrefixMasks ReportingHostPairSegments
set_option maxHeartbeats 600000

theorem ThreeSum.ReportingHostPrefixOrder.left_values {h J k : ℕ} (hk : k ≤ J) :
    RadixKeyLists.values ((2^(512*h) : ℕ) : ℤ) (leftMasks (512*h) h) k =
      (leftSets h J k).map (fun S => (subsetMask S : ℤ)) := by sorry
