-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_injective
-- name    : ThreeSum.ReportingHostSuffix.liftSet_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:20:35.252963+00:00
-- url     : https://prove2.me/theorems/bc460d18-fc2d-4dca-97e8-a99b0dd9f390
-- title:
--   Reporting Host Suffix: lift Set injective
-- statement:
--   The Reporting Host Suffix construction uses the lift Set injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L34-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L34-L35

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators

theorem ThreeSum.ReportingHostSuffix.liftSet_injective {W V offset : ℕ} (hfit : offset+V ≤ W) :
    Function.Injective (liftSet hfit) := by sorry
