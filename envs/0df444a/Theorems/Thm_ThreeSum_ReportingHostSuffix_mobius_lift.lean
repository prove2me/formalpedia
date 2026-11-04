-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffix_mobius_lift
-- name    : ThreeSum.ReportingHostSuffix.mobius_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:20:43.488811+00:00
-- url     : https://prove2.me/theorems/6dfc6077-ce75-48ce-b5e6-ead7de09b6ea
-- title:
--   Reporting Host Suffix: mobius lift
-- statement:
--   The Reporting Host Suffix construction uses the mobius lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L79-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L79-L84

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators

theorem ThreeSum.ReportingHostSuffix.mobius_lift {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin V))
    (f : Finset (Fin W) → ℤ) :
    Subset.mobius f (liftSet hfit Q) = Subset.mobius (fun S => f (liftSet hfit S)) Q := by sorry
