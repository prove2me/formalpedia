-- Prove2me | Theorems.Thm_ThreeSum_Radix_radix_divisibility_w3sum_ac885d1
-- name    : ThreeSum.Radix.radix_divisibility_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:03:04.632656+00:00
-- url     : https://prove2.me/theorems/91f4bf09-0e8b-4f76-9558-935f04f72ff2
-- title:
--   Radix: radix divisibility
-- statement:
--   Divisibility through one radix digit.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Radix.lean#L43-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Radix.lean#L43-L64

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

theorem ThreeSum.Radix.radix_divisibility_w3sum_ac885d1 (p a h t : ℤ) (hp : p ≠ 0) (j : ℕ) :
    p ^ (j + 1) ∣ a - (h + p * t) ↔
      p ∣ a - h ∧ p ^ j ∣ (a - h) / p - t := by sorry
