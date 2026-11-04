-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_right_mem_vertices
-- name    : ThreeSum.LocalGraph.right_mem_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:09.065238+00:00
-- url     : https://prove2.me/theorems/72339355-9047-442d-a57e-318928d725cc
-- title:
--   Local Graph: right mem vertices
-- statement:
--   The Local Graph construction uses the right mem vertices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L137-L138
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L137-L138

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

theorem ThreeSum.LocalGraph.right_mem_vertices (e : Edge L h) : right e ∈ rightVertices L h := by sorry
