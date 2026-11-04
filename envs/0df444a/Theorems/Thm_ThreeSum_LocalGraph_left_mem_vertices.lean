-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_left_mem_vertices
-- name    : ThreeSum.LocalGraph.left_mem_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:16.631093+00:00
-- url     : https://prove2.me/theorems/c257dcbb-db8f-48dc-a219-f995241f3ef7
-- title:
--   Local Graph: left mem vertices
-- statement:
--   The Local Graph construction uses the left mem vertices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L134-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L134-L135

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

theorem ThreeSum.LocalGraph.left_mem_vertices (e : Edge L h) : left e ∈ leftVertices L h := by sorry
