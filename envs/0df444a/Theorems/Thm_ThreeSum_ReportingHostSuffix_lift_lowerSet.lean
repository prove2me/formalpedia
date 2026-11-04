-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffix_lift_lowerSet
-- name    : ThreeSum.ReportingHostSuffix.lift_lowerSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:20:15.714768+00:00
-- url     : https://prove2.me/theorems/b69ac9c7-a767-4447-838d-d6960ecb7c47
-- title:
--   Reporting Host Suffix: lift lower Set
-- statement:
--   The Reporting Host Suffix construction uses the lift lower Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L58-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L58-L69

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators

theorem ThreeSum.ReportingHostSuffix.lift_lowerSet {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin W))
    (hQ : ∀ i ∈ Q, offset ≤ i.val ∧ i.val < offset+V) : liftSet hfit (lowerSet hfit Q) = Q := by sorry
