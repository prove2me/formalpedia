-- Prove2me | Theorems.Thm_Sendov_sendov
-- name    : Sendov.sendov
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T20:05:47.255748+00:00
-- url     : https://prove2.me/theorems/3814b7aa-d7b6-55f4-ab9f-9c7f7e524e33
-- title:
--   Sendov: sendov
-- statement:
--   **Sendov's conjecture.**  Every zero of a degree `n ≥ 2` polynomial with all zeroes in the
--   closed unit disk has a critical point within distance `1`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Conjecture.lean#L158-L167
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Conjecture.lean#L158-L167

import Definitions.Def_Sendov_Interior
import Definitions.Def_Sendov_Boundary
import Definitions.Def_Sendov_Conjecture
set_option autoImplicit false
open Sendov
open Polynomial

theorem Sendov.sendov {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ ≤ 1 := by sorry
