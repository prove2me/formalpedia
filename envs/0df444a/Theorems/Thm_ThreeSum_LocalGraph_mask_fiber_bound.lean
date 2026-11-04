-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_mask_fiber_bound
-- name    : ThreeSum.LocalGraph.mask_fiber_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:20.877588+00:00
-- url     : https://prove2.me/theorems/212ee587-9a86-48a3-b0e5-ef3eee782e10
-- title:
--   Local Graph: mask fiber bound
-- statement:
--   The Local Graph construction uses the mask fiber bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L197-L201
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L197-L201

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

theorem ThreeSum.LocalGraph.mask_fiber_bound (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h =>
      (fun i => left f i == right f i) = (fun i => left e i == right e i))).card ≤
      (2 * h).choose h := by sorry
