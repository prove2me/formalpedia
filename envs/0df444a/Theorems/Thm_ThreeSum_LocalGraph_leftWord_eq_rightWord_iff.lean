-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_leftWord_eq_rightWord_iff
-- name    : ThreeSum.LocalGraph.leftWord_eq_rightWord_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:06:58.162209+00:00
-- url     : https://prove2.me/theorems/4f78d4e9-0f65-4e94-bc5d-bac91337003e
-- title:
--   Local Graph: left Word eq right Word iff
-- statement:
--   The Local Graph construction uses the left Word eq right Word iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L37-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L37-L48

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LocalGraph
set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]

theorem ThreeSum.LocalGraph.leftWord_eq_rightWord_iff [Fintype α] (s v : Finset α) :
    leftWord s = rightWord v ↔ s = Finset.univ \ v := by sorry
