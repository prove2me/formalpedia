-- Prove2me | Theorems.Thm_QuadraticFloor_half_sum_zero_of_even
-- name    : QuadraticFloor.half_sum_zero_of_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:02:28.894178+00:00
-- url     : https://prove2.me/theorems/315ba335-a8ea-4cce-8b56-b23d26a83b08
-- title:
--   Quadratic Floor: half sum zero of even
-- statement:
--   **Lemma 3.1(2).** A function with `f(x + h) = -f(x)`, `f(0) = 0` and `f(2h - x) = f(x)` has
--   zero sum over `[1, h]`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L54-L56
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L54-L56

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.half_sum_zero_of_even (f : ℕ → ℂ) {h : ℕ} (hf : ∀ x, f (x + h) = -f x) (h0 : f 0 = 0)
    (hrefl : ∀ x ≤ 2 * h, f (2 * h - x) = f x) : ∑ x ∈ Icc 1 h, f x = 0 := by sorry
