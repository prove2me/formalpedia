-- Prove2me | Theorems.Thm_Sendov_Multiset_prod_le_mean_pow
-- name    : Sendov.Multiset.prod_le_mean_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:49:23.575973+00:00
-- url     : https://prove2.me/theorems/c9c7e4d0-ae69-4315-9989-e2a542ff0b48
-- title:
--   Multiset: prod le mean pow
-- statement:
--   **AM–GM for multisets.**  `∏ s ≤ (mean s) ^ card s`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Maclaurin.lean#L107-L143
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Maclaurin.lean#L107-L143

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

theorem Sendov.Multiset.prod_le_mean_pow : ∀ (s : Multiset ℝ), (∀ x ∈ s, 0 ≤ x) →
    s.prod ≤ (s.sum / s.card) ^ s.card := by sorry
