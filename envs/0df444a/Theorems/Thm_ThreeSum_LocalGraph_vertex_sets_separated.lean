-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_vertex_sets_separated
-- name    : ThreeSum.LocalGraph.vertex_sets_separated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:13.704204+00:00
-- url     : https://prove2.me/theorems/3279015f-4c9e-4f33-9352-e4274d377a89
-- title:
--   Local Graph: vertex sets separated
-- statement:
--   The Local Graph construction uses the vertex sets separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L140-L145
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L140-L145

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

theorem ThreeSum.LocalGraph.vertex_sets_separated (hsep : 2 * h < L)
    (s : Fin L → Bool) (hs : s ∈ leftVertices L h)
    (t : Fin L → Bool) (ht : t ∈ rightVertices L h) : s ≠ t := by sorry
