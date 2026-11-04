-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_mask_int
-- name    : ThreeSum.ReportingHostSuffix.liftSet_mask_int
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:21:05.705441+00:00
-- url     : https://prove2.me/theorems/d2aea3ac-421b-44c3-8098-c28afa6562a2
-- title:
--   Reporting Host Suffix: lift Set mask int
-- statement:
--   The Reporting Host Suffix construction uses the lift Set mask int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L45-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L45-L49

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators

theorem ThreeSum.ReportingHostSuffix.liftSet_mask_int {W V offset : ℕ} (hfit : offset+V ≤ W) (S : Finset (Fin V)) :
    (subsetMask (liftSet hfit S) : ℤ) = (2^offset : ℕ)*(subsetMask S : ℤ) := by sorry
