-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_equalityMask_eq_union
-- name    : ThreeSum.LocalGraph.equalityMask_eq_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:06:59.120509+00:00
-- url     : https://prove2.me/theorems/a77573f1-a848-4c37-80b6-ed37ac13d0e1
-- title:
--   Local Graph: equality Mask eq union
-- statement:
--   The equality mask is true exactly on the union of the disjoint endpoint
--   subsets. This identifies the exceptional four-word hash fibers.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L63-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L63-L68

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

theorem ThreeSum.LocalGraph.equalityMask_eq_union {s v : Finset α} (hd : Disjoint s v) :
    (fun i => leftWord s i == rightWord v i) = leftWord (s ∪ v) := by sorry
