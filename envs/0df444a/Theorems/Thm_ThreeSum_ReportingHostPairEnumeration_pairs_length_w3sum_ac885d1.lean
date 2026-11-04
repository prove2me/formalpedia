-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_pairs_length_w3sum_ac885d1
-- name    : ThreeSum.ReportingHostPairEnumeration.pairs_length_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:43:22.177976+00:00
-- url     : https://prove2.me/theorems/95825bae-aaaa-4100-8c90-dbc3843d8f95
-- title:
--   Reporting Host Pair Enumeration: pairs length
-- statement:
--   The Reporting Host Pair Enumeration construction uses the pairs length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPairEnumeration.lean#L93-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPairEnumeration.lean#L93-L107

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPairEnumeration
open Finset ThreeSum.SubsetAddress LayerCounts LocalGraph
set_option linter.unusedSimpArgs false

theorem ThreeSum.ReportingHostPairEnumeration.pairs_length_w3sum_ac885d1 (L h : ℕ) :
    (pairs L h).length = L.choose (2*h)*(2*h).choose h := by sorry
