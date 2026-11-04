-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_subset
-- name    : ThreeSum.ReportingHostSuffix.liftSet_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:21:03.136721+00:00
-- url     : https://prove2.me/theorems/b7d863c7-709a-4b7c-9097-86b8774b2d06
-- title:
--   Reporting Host Suffix: lift Set subset
-- statement:
--   The Reporting Host Suffix construction uses the lift Set subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L37-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L37-L38

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators

theorem ThreeSum.ReportingHostSuffix.liftSet_subset {W V offset : ℕ} (hfit : offset+V ≤ W) (S T : Finset (Fin V)) :
    liftSet hfit S ⊆ liftSet hfit T ↔ S ⊆ T := by sorry
