-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostFrontier_word_children
-- name    : ThreeSum.ReportingHostFrontier.word_children
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:32:07.637381+00:00
-- url     : https://prove2.me/theorems/4dfa80dc-34e4-4e6a-b7ed-48af7b4f9a27
-- title:
--   Reporting Host Frontier: word children
-- statement:
--   The Reporting Host Frontier construction uses the word children property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L50-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L50-L53

import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
import Definitions.Def_WeightedCache3SUM_Alias_658daccd3d316101

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostFrontier
open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostFrontier.word_children {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (r : RawItem h J α β γ) (hr : r ∈ domain I w) (j : ℕ) (hj : j < J) :
    (word r)[j]'(by rw [word,partitionWord_length]; exact hj) ∈ children w.2.2 j := by sorry
