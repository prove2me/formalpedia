-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_leftWord_injective
-- name    : ThreeSum.LocalGraph.leftWord_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:06:58.300225+00:00
-- url     : https://prove2.me/theorems/aeb9fb4d-233d-43d8-aae5-657394a6dccd
-- title:
--   Local Graph: left Word injective
-- statement:
--   The Local Graph construction uses the left Word injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L26-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L26-L29

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

theorem ThreeSum.LocalGraph.leftWord_injective : Function.Injective (@leftWord α _) := by sorry
