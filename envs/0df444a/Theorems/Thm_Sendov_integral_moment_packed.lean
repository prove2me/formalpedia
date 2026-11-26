-- Prove2me | Theorems.Thm_Sendov_integral_moment_packed
-- name    : Sendov.integral_moment_packed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:11.47774+00:00
-- url     : https://prove2.me/theorems/c8c3847f-2c6d-55b3-9bea-273d59125361
-- title:
--   Sendov: integral moment packed
-- statement:
--   **The moment from a verified numerator.**  Combining `Sendov.integral_moment_of` with
--   `Sendov.pev_wsum`, the integral is an explicit integer polynomial over an explicit
--   denominator.  Everything on the right is either supplied by the generator or a kernel
--   computation on integers.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L602-L619
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L602-L619

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.integral_moment_packed (n k : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : 0 ≤ α)
    (L : ℤ) (hL : 0 < L) (Nmom : List ℤ)
    (hdvd : ∀ j, j < 2 * k + 1 → ((0 : ℕ) + j + 4 : ℤ) ∣ L)
    (hNmom : pev Nmom α = pev (wsum L 0 (qrow (gg0 n) (gg1 n) (gg2 n) k)) α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ k)
      = pev Nmom α / ((L : ℝ) * (2 * M n * (3 + α)) ^ k) := by sorry
