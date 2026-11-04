-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostFrontier_mem_frontier_iff_w3sum_ac885d1
-- name    : ThreeSum.ReportingHostFrontier.mem_frontier_iff_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:32:28.602456+00:00
-- url     : https://prove2.me/theorems/27509625-9d73-4a1d-ab49-3b20425e1619
-- title:
--   Reporting Host Frontier: mem frontier iff
-- statement:
--   The Reporting Host Frontier construction uses the mem frontier iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L55-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L55-L68

import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
import Theorems.Thm_ThreeSum_RawReporting_mem_frontier_iff
import Definitions.Def_WeightedCache3SUM_Alias_c2dccdb99e31a4aa

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostFrontier
open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostFrontier.mem_frontier_iff_w3sum_ac885d1 {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (hk : k ≤ J) (pre : List (Finset (Fin (512*h)))) :
    pre ∈ frontier I w k ↔ ∃ r ∈ I, wantedOf r = w ∧ (word r).take k = pre := by sorry
