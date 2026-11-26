-- Prove2me | Theorems.Thm_Sendov_amgm_step
-- name    : Sendov.amgm_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:48:53.40267+00:00
-- url     : https://prove2.me/theorems/86f036d7-cb7f-43a7-be93-f88437a11a9c
-- title:
--   Sendov: amgm step
-- statement:
--   The AM–GM induction step: `a uᴺ ≤ μ^{N+1}` where `μ` is the mean of `a` together with `N`
--   copies of `u`.  Dividing by `u^{N+1}` this is Bernoulli.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Maclaurin.lean#L54-L72
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Maclaurin.lean#L54-L72

import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Definitions.Def_Sendov_Analytic_Maclaurin
set_option autoImplicit false
open Sendov
open Multiset
variable {a : ℝ} {t : Multiset ℝ}

theorem Sendov.amgm_step (N : ℕ) {u : ℝ} (hu : 0 < u) (ha : 0 ≤ a) :
    a * u ^ N ≤ ((a + N * u) / (N + 1)) ^ (N + 1) := by sorry
