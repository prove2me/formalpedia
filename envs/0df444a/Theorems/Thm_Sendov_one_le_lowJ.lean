-- Prove2me | Theorems.Thm_Sendov_one_le_lowJ
-- name    : Sendov.one_le_lowJ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:58:11.621709+00:00
-- url     : https://prove2.me/theorems/2740f483-a050-436e-a07c-39bae0b70e5a
-- title:
--   Sendov: one le low J
-- statement:
--   The branch point `(⋆)`, with every factor replaced by the scalar `X(t)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/LowDegree.lean#L93-L105
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/LowDegree.lean#L93-L105

import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
set_option autoImplicit false
open Sendov

theorem Sendov.one_le_lowJ {n : ℕ} {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {q : Multiset ℂ} (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) :
    1 ≤ lowJ (n - 1) a := by sorry
