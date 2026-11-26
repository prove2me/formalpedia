-- Prove2me | Theorems.Thm_Sendov_all_q_eq_one
-- name    : Sendov.all_q_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:58:56.305929+00:00
-- url     : https://prove2.me/theorems/0b05718b-17c1-5cd0-9586-a30873433876
-- title:
--   Sendov: all q eq one
-- statement:
--   Both sides of `(BR)` are pinned: the left has real part at most `N`, the right at least `N`,
--   so every `qⱼ` has real part `1` and hence, lying in the closed unit disk, equals `1`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Boundary.lean#L168-L205
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Boundary.lean#L168-L205

import Definitions.Def_Sendov_Counterexample_Factor
import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Boundary
set_option autoImplicit false
open Sendov
open Polynomial

theorem Sendov.all_q_eq_one {N : ℕ} {qs zs : Multiset ℂ}
    (hqcard : qs.card = N) (hzcard : zs.card = N)
    (hq1 : ∀ v ∈ qs, ‖v‖ ≤ 1) (hz1 : ∀ w ∈ zs, ‖w‖ ≤ 1) (hzne : ∀ w ∈ zs, w ≠ 1)
    (hBR : qs.sum = 2 * (zs.map (fun w => ((1 : ℂ) - w)⁻¹)).sum) :
    ∀ v ∈ qs, v = 1 := by sorry
