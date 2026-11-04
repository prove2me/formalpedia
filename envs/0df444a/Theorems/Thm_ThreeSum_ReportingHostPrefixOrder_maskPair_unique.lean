-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixOrder_maskPair_unique
-- name    : ThreeSum.ReportingHostPrefixOrder.maskPair_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:57:54.328249+00:00
-- url     : https://prove2.me/theorems/ca3ab2bf-9517-4461-9c45-206c4db264cc
-- title:
--   Reporting Host Prefix Order: mask Pair unique
-- statement:
--   The Reporting Host Prefix Order construction uses the mask Pair unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixOrder.lean#L90-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixOrder.lean#L90-L97

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixOrder
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPairEnumeration
open ReportingHostPrefixMasks ReportingHostPairSegments
set_option maxHeartbeats 600000

theorem ThreeSum.ReportingHostPrefixOrder.maskPair_unique {h J k i j : ℕ} (hk : k ≤ J)
    (hi : i < (prefixes h k).length) (hj : j < (prefixes h k).length)
    (hL : subsetMask (preL h J k i) = subsetMask (preL h J k j))
    (hR : subsetMask (preR h J k i) = subsetMask (preR h J k j)) : i=j := by sorry
