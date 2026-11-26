-- Prove2me | Theorems.Thm_QuadraticFloor_sum_range_mul
-- name    : QuadraticFloor.sum_range_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:49:21.790301+00:00
-- url     : https://prove2.me/theorems/e6ea945e-2b70-5fec-bf5f-0008215480fa
-- title:
--   Quadratic Floor: sum range mul
-- statement:
--   The Quadratic Floor construction uses the sum range mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/HalfPeriod.lean#L81-L85
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/HalfPeriod.lean#L81-L85

module
public import Definitions.Def_QuadraticFloor_Eta
public import Definitions.Def_QuadraticFloor_HalfPeriod
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.sum_range_mul {M : Type*} [AddCommMonoid M] (F : ℕ → M) (m n : ℕ) :
    ∑ x ∈ range (m * n), F x = ∑ k ∈ range n, ∑ y ∈ range m, F (m * k + y) := by sorry
