-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffix_lift_localQuery
-- name    : ThreeSum.ReportingHostSuffix.lift_localQuery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:20:38.342293+00:00
-- url     : https://prove2.me/theorems/692c4a3b-eead-415b-bba3-f61b1c363ce1
-- title:
--   Reporting Host Suffix: lift local Query
-- statement:
--   The Reporting Host Suffix construction uses the lift local Query property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L122-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L122-L124

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators

theorem ThreeSum.ReportingHostSuffix.lift_localQuery {J L k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L)) :
    liftSet (block_fit hk) (localQuery hk Q) = querySet k Q := by sorry
