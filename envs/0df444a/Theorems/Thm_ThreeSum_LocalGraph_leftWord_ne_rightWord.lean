-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_leftWord_ne_rightWord
-- name    : ThreeSum.LocalGraph.leftWord_ne_rightWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:06:59.956628+00:00
-- url     : https://prove2.me/theorems/050370f5-8efc-44c1-9324-a8aaace9faf7
-- title:
--   Local Graph: left Word ne right Word
-- statement:
--   With `2*h<L`, no left vertex word can equal any right vertex word, even
--   when the two vertices do not form an edge.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L52-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L52-L59

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

theorem ThreeSum.LocalGraph.leftWord_ne_rightWord {L h : ℕ} {s v : Finset (Fin L)}
    (hs : s.card = h) (hv : v.card = h) (hsep : 2 * h < L) :
    leftWord s ≠ rightWord v := by sorry
