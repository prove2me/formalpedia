-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_rightVertices_card
-- name    : ThreeSum.LocalGraph.rightVertices_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:09.244743+00:00
-- url     : https://prove2.me/theorems/f30d7faa-357b-4423-bb12-e38efb7d1f7e
-- title:
--   Local Graph: right Vertices card
-- statement:
--   The Local Graph construction uses the right Vertices card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L131-L132
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L131-L132

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

theorem ThreeSum.LocalGraph.rightVertices_card (L h : ℕ) : (rightVertices L h).card = L.choose h := by sorry
