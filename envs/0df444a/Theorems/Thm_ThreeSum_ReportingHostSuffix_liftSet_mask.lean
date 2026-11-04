-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_mask
-- name    : ThreeSum.ReportingHostSuffix.liftSet_mask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:20:36.934955+00:00
-- url     : https://prove2.me/theorems/a04d0ab1-bc3e-42ae-abed-61c3cccc75a6
-- title:
--   Reporting Host Suffix: lift Set mask
-- statement:
--   The Reporting Host Suffix construction uses the lift Set mask property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L40-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L40-L43

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators

theorem ThreeSum.ReportingHostSuffix.liftSet_mask {W V offset : ℕ} (hfit : offset+V ≤ W) (S : Finset (Fin V)) :
    subsetMask (liftSet hfit S) = 2^offset*subsetMask S := by sorry
