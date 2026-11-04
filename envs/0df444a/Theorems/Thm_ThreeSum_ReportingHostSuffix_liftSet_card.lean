-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_card
-- name    : ThreeSum.ReportingHostSuffix.liftSet_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:19:56.744358+00:00
-- url     : https://prove2.me/theorems/7a27114e-5585-4cd7-bf1e-0aedb8b833d5
-- title:
--   Reporting Host Suffix: lift Set card
-- statement:
--   The Reporting Host Suffix construction uses the lift Set card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L28-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L28-L29

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators

theorem ThreeSum.ReportingHostSuffix.liftSet_card {W V offset : ℕ} (hfit : offset+V ≤ W) (S : Finset (Fin V)) :
    (liftSet hfit S).card = S.card := by sorry
