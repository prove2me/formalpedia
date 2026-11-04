-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostFrontier_candidates_length
-- name    : ThreeSum.ReportingHostFrontier.candidates_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:31:40.983702+00:00
-- url     : https://prove2.me/theorems/1a721a81-07dc-44bc-8d16-a2f3186c5e06
-- title:
--   Reporting Host Frontier: candidates length
-- statement:
--   The Reporting Host Frontier construction uses the candidates length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L106-L109
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L106-L109

import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostFrontier
open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
omit [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostFrontier.candidates_length {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (hk : k < J) :
    (candidates I w k).length = (frontier I w k).length*groupSize h := by sorry
