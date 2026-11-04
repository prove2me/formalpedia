-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffix_mem_lowerSet
-- name    : ThreeSum.ReportingHostSuffix.mem_lowerSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:19:47.295536+00:00
-- url     : https://prove2.me/theorems/683e7e86-f0a6-442a-b30e-2aa343d8da70
-- title:
--   Reporting Host Suffix: mem lower Set
-- statement:
--   The Reporting Host Suffix construction uses the mem lower Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L54-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L54-L56

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators

theorem ThreeSum.ReportingHostSuffix.mem_lowerSet {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin W))
    (i : Fin V) : i ∈ lowerSet hfit Q ↔ shiftEmbedding offset hfit i ∈ Q := by sorry
