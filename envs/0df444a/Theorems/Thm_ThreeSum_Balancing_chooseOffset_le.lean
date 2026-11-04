-- Prove2me | Theorems.Thm_ThreeSum_Balancing_chooseOffset_le
-- name    : ThreeSum.Balancing.chooseOffset_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:35.842851+00:00
-- url     : https://prove2.me/theorems/d559deb7-d8d5-4b52-a8ef-3aa3b11b9c35
-- title:
--   Balancing: choose Offset le
-- statement:
--   The Balancing construction uses the choose Offset le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Balancing.lean#L45-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Balancing.lean#L45-L54

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

theorem ThreeSum.Balancing.chooseOffset_le [Inhabited G] (keys : List G) (F H : G → ℕ)
    {d : G} (hd : d ∈ keys) :
    correlation F H (chooseOffset keys F H) ≤ correlation F H d := by sorry
