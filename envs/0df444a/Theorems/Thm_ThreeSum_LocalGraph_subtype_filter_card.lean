-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_subtype_filter_card
-- name    : ThreeSum.LocalGraph.subtype_filter_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:11.693477+00:00
-- url     : https://prove2.me/theorems/7f3ea35d-eb7c-4bff-aa1e-d0608c4c5d3f
-- title:
--   Local Graph: subtype filter card
-- statement:
--   Transfer counts in a finite subtype to counts in its actual enumerated
--   domain. This lemma introduces no larger sample space.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L149-L159
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L149-L159

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

theorem ThreeSum.LocalGraph.subtype_filter_card {β : Type*} [DecidableEq β] (s : Finset β)
    (p : β → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun e : s => p e.val)).card = (s.filter p).card := by sorry
