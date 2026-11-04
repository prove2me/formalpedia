-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_rightAt_eq_get
-- name    : ThreeSum.ReportingHostPairEnumeration.rightAt_eq_get
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:43:07.263699+00:00
-- url     : https://prove2.me/theorems/6675eb08-c10f-4072-b4e3-8e41c4fba14d
-- title:
--   Reporting Host Pair Enumeration: right At eq get
-- statement:
--   The Reporting Host Pair Enumeration construction uses the right At eq get property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPairEnumeration.lean#L121-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPairEnumeration.lean#L121-L124

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPairEnumeration
open Finset ThreeSum.SubsetAddress LayerCounts LocalGraph
set_option linter.unusedSimpArgs false

theorem ThreeSum.ReportingHostPairEnumeration.rightAt_eq_get {L h i j : ℕ} (hi : i < L.choose h) (hj : j < (L-h).choose h) :
    rightAt L h i j = (rights (leftAt L h i) h)[j]'(by rw [rights_length _ (leftAt_card hi)]; exact hj) := by sorry
