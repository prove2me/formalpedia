-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_left_fiber_card
-- name    : ThreeSum.LocalGraph.left_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:14.256703+00:00
-- url     : https://prove2.me/theorems/713f1546-5165-41a3-8590-3abb5d3a0925
-- title:
--   Local Graph: left fiber card
-- statement:
--   Every endpoint has exactly the combinatorial degree, expressed on the
--   edge subtype used by the finite hash experiment.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L167-L172
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L167-L172

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

theorem ThreeSum.LocalGraph.left_fiber_card (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h => left f = left e)).card =
      (L - h).choose h := by sorry
