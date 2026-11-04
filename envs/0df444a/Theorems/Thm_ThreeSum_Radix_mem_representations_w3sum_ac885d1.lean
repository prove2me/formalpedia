-- Prove2me | Theorems.Thm_ThreeSum_Radix_mem_representations_w3sum_ac885d1
-- name    : ThreeSum.Radix.mem_representations_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:03:07.193465+00:00
-- url     : https://prove2.me/theorems/c2d0ee54-dcd3-4662-9bb7-a5cddbed370a
-- title:
--   Radix: mem representations
-- statement:
--   The recursive family contains exactly all positional representations,
--   including their distinct schedules and local edge choices.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Radix.lean#L68-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Radix.lean#L68-L87

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Aesop
import Definitions.Def_Submission_ThreeSum_Radix
set_option autoImplicit false
open ThreeSum ThreeSum.Radix
open Finset
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem ThreeSum.Radix.mem_representations_w3sum_ac885d1 (p : ℤ) (hp : p ≠ 0) (left right : Ω → ℤ)
    (j : ℕ) (a b : ℤ) (xs : List Ω) :
    xs ∈ representations p left right j a b ↔
      xs.length = j ∧ p ^ j ∣ a - positionalHash p left xs ∧
        p ^ j ∣ b - positionalHash p right xs := by sorry
