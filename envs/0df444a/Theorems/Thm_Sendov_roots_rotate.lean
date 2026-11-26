-- Prove2me | Theorems.Thm_Sendov_roots_rotate
-- name    : Sendov.roots_rotate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T20:06:07.192626+00:00
-- url     : https://prove2.me/theorems/66123cf7-d18e-5132-9b81-27eef9135b0b
-- title:
--   Sendov: roots rotate
-- statement:
--   The Sendov construction uses the roots rotate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Conjecture.lean#L68-L76
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Conjecture.lean#L68-L76

import Definitions.Def_Sendov_Interior
import Definitions.Def_Sendov_Boundary
import Definitions.Def_Sendov_Conjecture
set_option autoImplicit false
open Sendov
open Polynomial

theorem Sendov.roots_rotate {ω : ℂ} (hω : ‖ω‖ = 1) {p : ℂ[X]} (hp : p ≠ 0)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) : ∀ w ∈ (rotate ω p).roots, ‖w‖ ≤ 1 := by sorry
