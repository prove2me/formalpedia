-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_endpoint_injective
-- name    : ThreeSum.LocalGraph.endpoint_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:03.895297+00:00
-- url     : https://prove2.me/theorems/27c4fc43-5450-4c22-b424-2f4128a7f19a
-- title:
--   Local Graph: endpoint injective
-- statement:
--   The Local Graph construction uses the endpoint injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L103-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L103-L108

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

theorem ThreeSum.LocalGraph.endpoint_injective :
    Function.Injective (fun e : Edge L h => (left e, right e)) := by sorry
