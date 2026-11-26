-- Prove2me | Theorems.Thm_Sendov_esymm_card_cons
-- name    : Sendov.esymm_card_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:49:41.541398+00:00
-- url     : https://prove2.me/theorems/195e9770-0d42-43f8-914f-a4aeb3fc555d
-- title:
--   Sendov: esymm card cons
-- statement:
--   Splitting off one element: `E (a ::ₘ t) = ∏ t + a · E t`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Maclaurin.lean#L148-L163
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Maclaurin.lean#L148-L163

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

theorem Sendov.esymm_card_cons (a : ℝ) (t : Multiset ℝ) (ht : t ≠ 0) :
    (a ::ₘ t).esymm t.card = t.prod + a * t.esymm (t.card - 1) := by sorry
