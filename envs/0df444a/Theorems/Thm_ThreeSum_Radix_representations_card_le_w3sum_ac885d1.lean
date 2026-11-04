-- Prove2me | Theorems.Thm_ThreeSum_Radix_representations_card_le_w3sum_ac885d1
-- name    : ThreeSum.Radix.representations_card_le_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:03:07.842573+00:00
-- url     : https://prove2.me/theorems/2761f354-111c-4c89-8306-f267f1418447
-- title:
--   Radix: representations card le
-- statement:
--   Multiplicity compounds once per local choice; there is no extra carry
--   factor in the global bound.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Radix.lean#L103-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Radix.lean#L103-L120

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

theorem ThreeSum.Radix.representations_card_le_w3sum_ac885d1 (p : ℤ) (left right : Ω → ℤ) (B : ℕ)
    (hcap : ∀ a b, (localFiber p left right a b).card ≤ B)
    (j : ℕ) (a b : ℤ) : (representations p left right j a b).card ≤ B ^ j := by sorry
