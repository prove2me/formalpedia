-- Prove2me | Theorems.Thm_Sendov_alpha_le_half_M
-- name    : Sendov.alpha_le_half_M
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:20.243357+00:00
-- url     : https://prove2.me/theorems/51397380-e0e4-45ad-b1f9-c017fe448a86
-- title:
--   Sendov: alpha le half M
-- statement:
--   Feasibility bounds `α` by `(n-1)/2`, simply because it forces `A = 1 - 2α/(n-1) ≥ 0`.
--
--   This crude consequence is all that the *numerical* step of any degree needs: on
--   `0 ≤ α ≤ min 17 ((n-1)/2)` the upper bounds for `R n α` used in this development stay below
--   `0.856` for every `5 ≤ n ≤ 97`.  The exact shape of the feasible region, which is cut out
--   by a quartic in `α`, is therefore never required by the polynomial certificates.
--
--   This must not be read as saying that `A ≥ 0` replaces feasibility everywhere.  It does not:
--   the odd-degree bound needs `0 ≤ Q n α t` on `[0,1]`, which is `Sendov.Q_nonneg` and uses the
--   full constraint `c ^ 2 ≤ A` — it does not follow from `A ≥ 0`.  Accordingly
--   `Sendov.integral_rpow_le` takes `hfeas` itself, and only the passage from the resulting
--   rational function to a polynomial positivity statement is weakened to `α ≤ M n / 2`.  For
--   even degrees the moment identity `Sendov.integral_moment` needs no hypothesis at all.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Basic.lean#L58-L64
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Basic.lean#L58-L64

import Definitions.Def_Sendov_Defs
import Definitions.Def_Sendov_Common_Basic
set_option autoImplicit false
open Sendov
variable {n : ℕ} {α t : ℝ}

theorem Sendov.alpha_le_half_M (hn : 2 ≤ n) (hfeas : c n α ^ 2 ≤ A n α) : α ≤ M n / 2 := by sorry
