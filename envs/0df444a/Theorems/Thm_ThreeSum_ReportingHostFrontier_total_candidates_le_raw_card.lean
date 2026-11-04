-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostFrontier_total_candidates_le_raw_card
-- name    : ThreeSum.ReportingHostFrontier.total_candidates_le_raw_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:32:52.214194+00:00
-- url     : https://prove2.me/theorems/5447a40e-8d20-478e-980c-2ce4315837da
-- title:
--   Reporting Host Frontier: total candidates le raw card
-- statement:
--   The Reporting Host Frontier construction uses the total candidates le raw card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L111-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L111-L115

import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostFrontier
open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostFrontier.total_candidates_le_raw_card {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (hk : k < J) :
    (∑ w : Wanted h J α, (candidates I w k).length) ≤ I.card*groupSize h := by sorry
