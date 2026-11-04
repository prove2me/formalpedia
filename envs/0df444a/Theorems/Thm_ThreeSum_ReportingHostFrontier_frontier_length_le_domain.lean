-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostFrontier_frontier_length_le_domain
-- name    : ThreeSum.ReportingHostFrontier.frontier_length_le_domain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:31:34.846092+00:00
-- url     : https://prove2.me/theorems/176b5d10-6371-4863-9b0b-00f891be159d
-- title:
--   Reporting Host Frontier: frontier length le domain
-- statement:
--   The Reporting Host Frontier construction uses the frontier length le domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L75-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L75-L81

import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
import Theorems.Thm_ThreeSum_RawReporting_frontier_length_le_domain

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostFrontier
open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostFrontier.frontier_length_le_domain {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (hk : k ≤ J) : (frontier I w k).length ≤ (domain I w).card := by sorry
