-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffix_sum_powerset_lift
-- name    : ThreeSum.ReportingHostSuffix.sum_powerset_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:20:17.636703+00:00
-- url     : https://prove2.me/theorems/b9190c85-c23f-4312-9ddf-4797f5b0996e
-- title:
--   Reporting Host Suffix: sum powerset lift
-- statement:
--   The Reporting Host Suffix construction uses the sum powerset lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L71-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L71-L77

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators

theorem ThreeSum.ReportingHostSuffix.sum_powerset_lift {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin V))
    (f : Finset (Fin W) → ℤ) :
    (∑ S ∈ (liftSet hfit Q).powerset, f S) = ∑ S ∈ Q.powerset, f (liftSet hfit S) := by sorry
