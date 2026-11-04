-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_output_card
-- name    : ThreeSum.LocalGraph.output_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:04.327198+00:00
-- url     : https://prove2.me/theorems/ed6c593b-9fc6-4850-8693-953588bb36a9
-- title:
--   Local Graph: output card
-- statement:
--   The Local Graph construction uses the output card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L98-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L98-L101

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

theorem ThreeSum.LocalGraph.output_card (e : Edge L h) : (output e).card = 2 * h := by sorry
