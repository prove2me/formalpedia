-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_edge_card
-- name    : ThreeSum.LocalGraph.edge_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:11.993356+00:00
-- url     : https://prove2.me/theorems/291abddf-0b65-4bbe-b763-407332acb171
-- title:
--   Local Graph: edge card
-- statement:
--   The Local Graph construction uses the edge card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L161-L163
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L161-L163

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

theorem ThreeSum.LocalGraph.edge_card (L h : ℕ) :
    Fintype.card (Edge L h) = L.choose (2 * h) * (2 * h).choose h := by sorry
