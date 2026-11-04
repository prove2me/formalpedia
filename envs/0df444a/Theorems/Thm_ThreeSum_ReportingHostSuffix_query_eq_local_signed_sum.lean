-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffix_query_eq_local_signed_sum
-- name    : ThreeSum.ReportingHostSuffix.query_eq_local_signed_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:24:50.872854+00:00
-- url     : https://prove2.me/theorems/a0b930c1-8b00-4548-966c-ba0c7449f8ef
-- title:
--   Reporting Host Suffix: query eq local signed sum
-- statement:
--   The Reporting Host Suffix construction uses the query eq local signed sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L99-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L99-L105

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators

theorem ThreeSum.ReportingHostSuffix.query_eq_local_signed_sum {W V offset : ℕ} (hfit : offset+V ≤ W)
    (f g : Finset (Fin W) → ℤ) (stage : ℕ) (preL preR : Finset (Fin W)) (Q : Finset (Fin V)) :
    Subset.mobius (fun S => SubsetStages.stageValue f stage (preL ∪ S)*
      SubsetStages.stageValue g stage (preR ∪ S)) (liftSet hfit Q) =
        (-1 : ℤ)^Q.card * ∑ S ∈ Q.powerset, leafWeight hfit f g stage preL preR S := by sorry
