-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostFrontier_generationWork_le
-- name    : ThreeSum.ReportingHostFrontier.generationWork_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:32:22.562322+00:00
-- url     : https://prove2.me/theorems/fcc7bfe2-da7a-47fe-a291-d9748c6b1c7e
-- title:
--   Reporting Host Frontier: generation Work le
-- statement:
--   The Reporting Host Frontier construction uses the generation Work le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L122-L126
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L122-L126

import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostFrontier
open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostFrontier.generationWork_le {h J k : ℕ} (I : Finset (RawItem h J α β γ)) (hk : k < J) :
    generationWork I k ≤ I.card*(1600*(J*(512*h)+1)^2*(groupSize h+1)) := by sorry
