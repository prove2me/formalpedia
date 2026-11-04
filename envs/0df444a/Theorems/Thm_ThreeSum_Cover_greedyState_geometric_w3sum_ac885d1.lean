-- Prove2me | Theorems.Thm_ThreeSum_Cover_greedyState_geometric_w3sum_ac885d1
-- name    : ThreeSum.Cover.greedyState_geometric_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:33.777175+00:00
-- url     : https://prove2.me/theorems/0111e9aa-2ffa-47dd-92df-9da4e7f33028
-- title:
--   Cover: greedy State geometric
-- statement:
--   The exact geometric recurrence, with all denominators cleared.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Greedy.lean#L98-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Greedy.lean#L98-L115

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

theorem ThreeSum.Cover.greedyState_geometric_w3sum_ac885d1 [Fintype Ω] (maps : List Ω)
    (hall : ∀ ω, ω ∈ maps) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) (a : ℕ) (ha : 0 < a)
    (hfrequency : ∀ u ∈ targets,
      Fintype.card Ω ≤ a * (univ.filter fun ω => covers ω u).card) (t : ℕ) :
    a ^ t * (greedyState maps covers targets t).card ≤ (a - 1) ^ t * targets.card := by sorry
