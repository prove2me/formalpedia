-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_right_fiber_card
-- name    : ThreeSum.LocalGraph.right_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:13.895219+00:00
-- url     : https://prove2.me/theorems/b4b683ae-1b9a-4e8c-abad-69b4bf684b85
-- title:
--   Local Graph: right fiber card
-- statement:
--   The Local Graph construction uses the right fiber card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L174-L179
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L174-L179

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
open LayerCounts
variable {L h : ℕ}

theorem ThreeSum.LocalGraph.right_fiber_card (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h => right f = right e)).card =
      (L - h).choose h := by sorry
