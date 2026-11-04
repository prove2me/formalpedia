-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostFrontier_total_frontier_length_le_raw_card
-- name    : ThreeSum.ReportingHostFrontier.total_frontier_length_le_raw_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:33:32.654787+00:00
-- url     : https://prove2.me/theorems/e53f6485-05b9-4ec2-a0c4-eccb5fe478d8
-- title:
--   Reporting Host Frontier: total frontier length le raw card
-- statement:
--   The Reporting Host Frontier construction uses the total frontier length le raw card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L83-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L83-L90

import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
import Theorems.Thm_ThreeSum_RawReporting_total_frontier_length_le_raw_card

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostFrontier
open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostFrontier.total_frontier_length_le_raw_card {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (hk : k ≤ J) : (∑ w : Wanted h J α, (frontier I w k).length) ≤ I.card := by sorry
