-- Prove2me | Theorems.Thm_Sendov_low_degree_contradiction
-- name    : Sendov.low_degree_contradiction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T19:06:26.840892+00:00
-- url     : https://prove2.me/theorems/63a9bbe5-2efc-48f8-9e8a-ed863e14b19f
-- title:
--   Sendov: low degree contradiction
-- statement:
--   **The low-degree branch.**  The branch point `(⋆)` is already contradictory for
--   `2 ≤ n ≤ 5`, with no recourse to the origin channel.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/LowDegree.lean#L210-L218
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/LowDegree.lean#L210-L218

import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
set_option autoImplicit false
open Sendov

theorem Sendov.low_degree_contradiction {n : ℕ} (hn : 2 ≤ n) (hn5 : n ≤ 5) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) :
    False := by sorry
