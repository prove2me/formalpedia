-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_leftVertices_card
-- name    : ThreeSum.LocalGraph.leftVertices_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:07.070833+00:00
-- url     : https://prove2.me/theorems/43774e82-ea17-4656-baef-364c1887871c
-- title:
--   Local Graph: left Vertices card
-- statement:
--   The Local Graph construction uses the left Vertices card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L128-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L128-L129

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

theorem ThreeSum.LocalGraph.leftVertices_card (L h : ℕ) : (leftVertices L h).card = L.choose h := by sorry
