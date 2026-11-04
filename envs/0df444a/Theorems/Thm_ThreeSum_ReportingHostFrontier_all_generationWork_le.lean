-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostFrontier_all_generationWork_le
-- name    : ThreeSum.ReportingHostFrontier.all_generationWork_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:32:55.334056+00:00
-- url     : https://prove2.me/theorems/963fe2aa-c746-4a56-ae99-360d133a2e48
-- title:
--   Reporting Host Frontier: all generation Work le
-- statement:
--   The Reporting Host Frontier construction uses the all generation Work le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L128-L136
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L128-L136

import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostFrontier
open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostFrontier.all_generationWork_le {h J K : ℕ} (I : Finset (RawItem h J α β γ)) (hK : K ≤ J) :
    (∑ k ∈ Finset.range K, generationWork I k) ≤
      K*I.card*(1600*(J*(512*h)+1)^2*(groupSize h+1)) := by sorry
