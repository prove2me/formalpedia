-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_equalityMask_eq_output
-- name    : ThreeSum.LocalGraph.equalityMask_eq_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:12.602057+00:00
-- url     : https://prove2.me/theorems/767c27b3-af67-41ae-bb4c-d4fdc8c47a94
-- title:
--   Local Graph: equality Mask eq output
-- statement:
--   The Local Graph construction uses the equality Mask eq output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L113-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L113-L115

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

theorem ThreeSum.LocalGraph.equalityMask_eq_output (e : Edge L h) :
    equalityMask e = leftWord (output e) := by sorry
