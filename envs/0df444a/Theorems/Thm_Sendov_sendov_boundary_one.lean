-- Prove2me | Theorems.Thm_Sendov_sendov_boundary_one
-- name    : Sendov.sendov_boundary_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T19:07:43.696189+00:00
-- url     : https://prove2.me/theorems/e4404ce1-fd28-4b85-ad2b-3c30b0e16153
-- title:
--   Sendov: sendov boundary one
-- statement:
--   The closed-disk form.  In the extremal case `p = c(Xⁿ - 1)` the only critical point is `0`,
--   at distance exactly `1` from the zero `1`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Boundary.lean#L327-L334
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Boundary.lean#L327-L334

import Definitions.Def_Sendov_Counterexample_Factor
import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Boundary
set_option autoImplicit false
open Sendov
open Polynomial

theorem Sendov.sendov_boundary_one {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) (hp1 : p.eval 1 = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - 1‖ ≤ 1 := by sorry
