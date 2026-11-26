-- Prove2me | Theorems.Thm_SendovConjecture_sendov
-- name    : SendovConjecture.sendov
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T20:42:50.046534+00:00
-- url     : https://prove2.me/theorems/e6cd4da5-fc57-4091-bf6a-b6cb3f899257
-- title:
--   Sendov Conjecture: sendov
-- statement:
--   **Sendov's conjecture**, proved in `Sendov.sendov`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Solution.lean#L30-L33
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Solution.lean#L30-L33

import Definitions.Def_Sendov_Conjecture
import Definitions.Def_Sendov_Solution
import Theorems.Thm_Sendov_sendov

set_option autoImplicit false
open SendovConjecture
open Polynomial

theorem SendovConjecture.sendov {p : ℂ[X]} (hdeg : 2 ≤ p.natDegree)
    (hzeroes : ∀ w : ℂ, p.eval w = 0 → ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ ≤ 1 := by sorry
