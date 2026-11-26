-- Prove2me | Theorems.Thm_SendovConjecture_phelps_rodriguez
-- name    : SendovConjecture.phelps_rodriguez
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T20:41:15.904109+00:00
-- url     : https://prove2.me/theorems/9ebfb235-9d9b-5933-ac3e-2a1174f16786
-- title:
--   Sendov Conjecture: phelps rodriguez
-- statement:
--   **The Phelps–Rodriguez conjecture**, proved in `Sendov.phelps_rodriguez`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Solution.lean#L36-L42
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Solution.lean#L36-L42

import Definitions.Def_Sendov_Conjecture
import Definitions.Def_Sendov_Solution
import Theorems.Thm_Sendov_phelps_rodriguez

set_option autoImplicit false
open SendovConjecture
open Polynomial

theorem SendovConjecture.phelps_rodriguez {p : ℂ[X]} (hdeg : 2 ≤ p.natDegree)
    (hzeroes : ∀ w : ℂ, p.eval w = 0 → ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    (∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ < 1)
      ∨ (‖a‖ = 1 ∧ ∃ c : ℂ, c ≠ 0 ∧
          p = C c * (X ^ p.natDegree - C (a ^ p.natDegree))) := by sorry
