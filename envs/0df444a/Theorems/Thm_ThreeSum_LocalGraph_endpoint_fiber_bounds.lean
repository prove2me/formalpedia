-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_endpoint_fiber_bounds
-- name    : ThreeSum.LocalGraph.endpoint_fiber_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:19.738621+00:00
-- url     : https://prove2.me/theorems/59509426-e3dc-4fd0-b67e-0cb7a538d7c4
-- title:
--   Local Graph: endpoint fiber bounds
-- statement:
--   The Local Graph construction uses the endpoint fiber bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L190-L195
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L190-L195

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

theorem ThreeSum.LocalGraph.endpoint_fiber_bounds (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h => left f = left e)).card ≤
        (L - h).choose h ∧
      (Finset.univ.filter (fun f : Edge L h => right f = right e)).card ≤
        (L - h).choose h := by sorry
