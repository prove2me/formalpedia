-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_cross_separated
-- name    : ThreeSum.LocalGraph.cross_separated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:08.965383+00:00
-- url     : https://prove2.me/theorems/cc4f7059-78ab-4826-94d2-00aa8f24aceb
-- title:
--   Local Graph: cross separated
-- statement:
--   The Local Graph construction uses the cross separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L110-L111
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L110-L111

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

theorem ThreeSum.LocalGraph.cross_separated (hsep : 2 * h < L) (e f : Edge L h) : left e ≠ right f := by sorry
