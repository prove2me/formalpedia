-- Prove2me | Theorems.Thm_ThreeSum_LayerCounts_unionFiber_card_w3sum_ac885d1
-- name    : ThreeSum.LayerCounts.unionFiber_card_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:04:43.546086+00:00
-- url     : https://prove2.me/theorems/d23ccb8f-0eb1-4a80-9889-99971b6413b0
-- title:
--   Layer Counts: union Fiber card
-- statement:
--   The Layer Counts construction uses the union Fiber card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LayerCounts.lean#L83-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LayerCounts.lean#L83-L107

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LayerCounts
set_option autoImplicit false
open ThreeSum ThreeSum.LayerCounts
open Finset

theorem ThreeSum.LayerCounts.unionFiber_card_w3sum_ac885d1 {L h : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = 2 * h) :
    ((edgeSet L h).filter (fun p => p.1 ∪ p.2 = Q)).card = (2 * h).choose h := by sorry
