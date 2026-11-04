-- Prove2me | Theorems.Thm_ThreeSum_Cover_greedyState_contract
-- name    : ThreeSum.Cover.greedyState_contract
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:34.661633+00:00
-- url     : https://prove2.me/theorems/0800d6ae-a9e9-4855-85a7-ac2fa5af13e1
-- title:
--   Cover: greedy State contract
-- statement:
--   The Cover construction uses the greedy State contract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Greedy.lean#L80-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Greedy.lean#L80-L95

import Definitions.Def_Submission_ThreeSum_Cover
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Ring
import Aesop
import Definitions.Def_Submission_ThreeSum_Greedy
set_option autoImplicit false
open ThreeSum ThreeSum.Cover
open Finset
open scoped BigOperators
variable {Ω U : Type*} [Inhabited Ω] [DecidableEq U]

theorem ThreeSum.Cover.greedyState_contract [Fintype Ω] (maps : List Ω)
    (hall : ∀ ω, ω ∈ maps) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) (a : ℕ) (ha : 0 < a)
    (hfrequency : ∀ u ∈ targets,
      Fintype.card Ω ≤ a * (univ.filter fun ω => covers ω u).card) (t : ℕ) :
    a * (greedyState maps covers targets (t + 1)).card ≤
      (a - 1) * (greedyState maps covers targets t).card := by sorry
