-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffix_block_query_in_range
-- name    : ThreeSum.ReportingHostSuffix.block_query_in_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:20:39.455921+00:00
-- url     : https://prove2.me/theorems/c4a9de4b-f3ee-48c7-9c7c-05d775e82cf3
-- title:
--   Reporting Host Suffix: block query in range
-- statement:
--   The Reporting Host Suffix construction uses the block query in range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L110-L117
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L110-L117

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators

theorem ThreeSum.ReportingHostSuffix.block_query_in_range {J L k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L))
    (i : Fin (J*L)) (hi : i ∈ querySet k Q) : k*L ≤ i.val ∧ i.val < k*L+(J-k)*L := by sorry
