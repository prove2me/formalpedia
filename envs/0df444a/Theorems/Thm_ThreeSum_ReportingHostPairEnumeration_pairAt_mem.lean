-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_pairAt_mem
-- name    : ThreeSum.ReportingHostPairEnumeration.pairAt_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:44:37.956104+00:00
-- url     : https://prove2.me/theorems/b4303e83-b71e-4028-8129-941fc25fb879
-- title:
--   Reporting Host Pair Enumeration: pair At mem
-- statement:
--   The Reporting Host Pair Enumeration construction uses the pair At mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPairEnumeration.lean#L126-L131
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPairEnumeration.lean#L126-L131

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPairEnumeration
open Finset ThreeSum.SubsetAddress LayerCounts LocalGraph
set_option linter.unusedSimpArgs false

theorem ThreeSum.ReportingHostPairEnumeration.pairAt_mem {L h i j : ℕ} (hi : i < L.choose h) (hj : j < (L-h).choose h) :
    (leftAt L h i,rightAt L h i j) ∈ edgeSet L h := by sorry
