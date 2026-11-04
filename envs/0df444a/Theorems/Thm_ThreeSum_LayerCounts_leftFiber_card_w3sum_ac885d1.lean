-- Prove2me | Theorems.Thm_ThreeSum_LayerCounts_leftFiber_card_w3sum_ac885d1
-- name    : ThreeSum.LayerCounts.leftFiber_card_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:04:42.747973+00:00
-- url     : https://prove2.me/theorems/84b9d763-5b53-4091-8b58-88be017bfeac
-- title:
--   Layer Counts: left Fiber card
-- statement:
--   The Layer Counts construction uses the left Fiber card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LayerCounts.lean#L37-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LayerCounts.lean#L37-L65

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

theorem ThreeSum.LayerCounts.leftFiber_card_w3sum_ac885d1 {L h : ℕ} (S : Finset (Fin L)) (hS : S.card = h) :
    ((edgeSet L h).filter (fun p => p.1 = S)).card = (L - h).choose h := by sorry
