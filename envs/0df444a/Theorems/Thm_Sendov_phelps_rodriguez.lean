-- Prove2me | Theorems.Thm_Sendov_phelps_rodriguez
-- name    : Sendov.phelps_rodriguez
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T20:05:44.622098+00:00
-- url     : https://prove2.me/theorems/d55a2e08-6d7f-47cf-a2ef-9f34ccce07dd
-- title:
--   Sendov: phelps rodriguez
-- statement:
--   **The Phelps–Rodriguez conjecture.**  Every zero `a` of a degree `n ≥ 2` polynomial with all
--   zeroes in the closed unit disk has a critical point strictly within distance `1`, unless `a` is
--   on the unit circle and `p` is a scalar multiple of `zⁿ - aⁿ`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Conjecture.lean#L83-L152
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Conjecture.lean#L83-L152

import Definitions.Def_Sendov_Interior
import Definitions.Def_Sendov_Boundary
import Definitions.Def_Sendov_Conjecture
set_option autoImplicit false
open Sendov
open Polynomial

theorem Sendov.phelps_rodriguez {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    (∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ < 1)
      ∨ (‖a‖ = 1 ∧ ∃ c : ℂ, c ≠ 0 ∧ p = C c * (X ^ n - C (a ^ n))) := by sorry
