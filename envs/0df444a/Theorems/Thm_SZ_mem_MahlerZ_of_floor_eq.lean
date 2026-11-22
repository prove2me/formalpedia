-- Prove2me | Theorems.Thm_SZ_mem_MahlerZ_of_floor_eq
-- name    : SZ.mem_MahlerZ_of_floor_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:41:09.405801+00:00
-- url     : https://prove2.me/theorems/527f7838-5cb2-4e48-9a31-5e3b14360102
-- title:
--   SZ: mem Mahler Z of floor eq
-- statement:
--   The workhorse: an explicit even integer sequence tracking the floors from `N` on.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Defs.lean#L97-L100
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Defs.lean#L97-L100

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Defs
set_option autoImplicit false
open SZ
open Int

theorem SZ.mem_MahlerZ_of_floor_eq {α ξ : ℝ} (hα : 1 < α) (hξ : ξ ≠ 0) (N : ℕ) (x : ℕ → ℤ)
    (hx : ∀ n : ℕ, N ≤ n → Even (x n)) (hfl : ∀ n : ℕ, N ≤ n → ⌊ξ * α ^ n⌋ = x n) :
    α ∈ MahlerZ := by sorry
