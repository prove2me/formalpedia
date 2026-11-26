-- Prove2me | Theorems.Thm_Sendov_Multiset_esymm_card_pred_le
-- name    : Sendov.Multiset.esymm_card_pred_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:54:20.863369+00:00
-- url     : https://prove2.me/theorems/4f6fbcf4-fdef-5b6b-bb0d-c770bd3ad93c
-- title:
--   Multiset: esymm card pred le
-- statement:
--   **Maclaurin's inequality, top case.**  `e_{N-1}(s) ≤ N (mean s)^{N-1}`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Maclaurin.lean#L166-L221
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Maclaurin.lean#L166-L221

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

theorem Sendov.Multiset.esymm_card_pred_le : ∀ (s : Multiset ℝ), (∀ x ∈ s, 0 ≤ x) → s ≠ 0 →
    s.esymm (s.card - 1) ≤ s.card * (s.sum / s.card) ^ (s.card - 1) := by sorry
