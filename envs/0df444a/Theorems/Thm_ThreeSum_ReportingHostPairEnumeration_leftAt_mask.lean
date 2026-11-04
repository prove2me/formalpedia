-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_leftAt_mask
-- name    : ThreeSum.ReportingHostPairEnumeration.leftAt_mask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:44:29.063586+00:00
-- url     : https://prove2.me/theorems/f034307e-8893-4eec-a36e-e007a8728121
-- title:
--   Reporting Host Pair Enumeration: left At mask
-- statement:
--   The Reporting Host Pair Enumeration construction uses the left At mask property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPairEnumeration.lean#L141-L148
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPairEnumeration.lean#L141-L148

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_length

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPairEnumeration
open Finset ThreeSum.SubsetAddress LayerCounts LocalGraph
set_option linter.unusedSimpArgs false

theorem ThreeSum.ReportingHostPairEnumeration.leftAt_mask {L h i : ℕ} (hi : i < L.choose h) :
    subsetMask (leftAt L h i) = (enumerateLayer L h)[i]'(by rw [enumerateLayer_length]; exact hi) := by sorry
