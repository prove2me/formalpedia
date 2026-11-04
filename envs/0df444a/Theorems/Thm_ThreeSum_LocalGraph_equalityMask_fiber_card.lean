-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_equalityMask_fiber_card
-- name    : ThreeSum.LocalGraph.equalityMask_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:17.12834+00:00
-- url     : https://prove2.me/theorems/027a60fb-72a9-4e7c-a370-746f0f700ae4
-- title:
--   Local Graph: equality Mask fiber card
-- statement:
--   The exceptional equality-mask group has exactly one edge for each
--   `h`-subset of its `2*h` output coordinates.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L183-L188
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L183-L188

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

theorem ThreeSum.LocalGraph.equalityMask_fiber_card (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h => equalityMask f = equalityMask e)).card =
      (2 * h).choose h := by sorry
