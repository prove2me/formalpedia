-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_rightWord_injective
-- name    : ThreeSum.LocalGraph.rightWord_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:06:57.016194+00:00
-- url     : https://prove2.me/theorems/f2ab1c18-36c7-43b4-9a83-c41016219dbe
-- title:
--   Local Graph: right Word injective
-- statement:
--   The Local Graph construction uses the right Word injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L31-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L31-L35

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

theorem ThreeSum.LocalGraph.rightWord_injective : Function.Injective (@rightWord α _) := by sorry
