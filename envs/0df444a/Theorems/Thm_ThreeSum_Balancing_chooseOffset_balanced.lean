-- Prove2me | Theorems.Thm_ThreeSum_Balancing_chooseOffset_balanced
-- name    : ThreeSum.Balancing.chooseOffset_balanced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:36.24005+00:00
-- url     : https://prove2.me/theorems/72f7cbd4-fe82-4041-af6b-e6b4c1351d99
-- title:
--   Balancing: choose Offset balanced
-- statement:
--   The Balancing construction uses the choose Offset balanced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Balancing.lean#L56-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Balancing.lean#L56-L61

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_Balancing
set_option autoImplicit false
open ThreeSum ThreeSum.Balancing
open Finset
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem ThreeSum.Balancing.chooseOffset_balanced [Inhabited G] (keys : List G) (hall : ∀ d, d ∈ keys)
    (F H : G → ℕ) :
    Fintype.card G * correlation F H (chooseOffset keys F H) ≤
      (∑ k, F k) * (∑ k, H k) := by sorry
