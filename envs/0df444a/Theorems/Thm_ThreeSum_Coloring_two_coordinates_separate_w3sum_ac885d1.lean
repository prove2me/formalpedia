-- Prove2me | Theorems.Thm_ThreeSum_Coloring_two_coordinates_separate_w3sum_ac885d1
-- name    : ThreeSum.Coloring.two_coordinates_separate_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:09:11.516216+00:00
-- url     : https://prove2.me/theorems/c129a977-1910-4c2c-99d7-d0a3b4be5498
-- title:
--   Coloring: two coordinates separate
-- statement:
--   Two coordinates suffice to distinguish any three different binary words.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Coloring.lean#L35-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Coloring.lean#L35-L54

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Image
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Coloring
set_option autoImplicit false
open ThreeSum ThreeSum.Coloring
variable {α : Type*}

theorem ThreeSum.Coloring.two_coordinates_separate_w3sum_ac885d1 {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    ∃ i j, (s i, s j) ≠ (t i, t j) ∧
      (s i, s j) ≠ (u i, u j) ∧ (t i, t j) ≠ (u i, u j) := by sorry
