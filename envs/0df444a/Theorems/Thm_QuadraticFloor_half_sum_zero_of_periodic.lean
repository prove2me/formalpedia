-- Prove2me | Theorems.Thm_QuadraticFloor_half_sum_zero_of_periodic
-- name    : QuadraticFloor.half_sum_zero_of_periodic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:02:02.861816+00:00
-- url     : https://prove2.me/theorems/5b860dea-ef93-5ed7-ba54-ff20389d30f1
-- title:
--   Quadratic Floor: half sum zero of periodic
-- statement:
--   **Lemma 3.1(1).** A function with `f(x + h) = f(x)` and zero sum over `[1, 2h]` has zero sum
--   over `[1, h]`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L48-L50
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L48-L50

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.half_sum_zero_of_periodic (f : ℕ → ℂ) {h : ℕ} (hf : ∀ x, f (x + h) = f x)
    (hfull : ∑ x ∈ Icc 1 (2 * h), f x = 0) : ∑ x ∈ Icc 1 h, f x = 0 := by sorry
