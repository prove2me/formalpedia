-- Prove2me | Theorems.Thm_QuadraticFloor_sum_Icc_one
-- name    : QuadraticFloor.sum_Icc_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:44:57.261083+00:00
-- url     : https://prove2.me/theorems/b588d730-6915-5096-9594-0007d56a66d8
-- title:
--   Quadratic Floor: sum Icc one
-- statement:
--   The Quadratic Floor construction uses the sum Icc one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/HalfPeriod.lean#L23-L26
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/HalfPeriod.lean#L23-L26

module
public import Definitions.Def_QuadraticFloor_Eta
public import Definitions.Def_QuadraticFloor_HalfPeriod
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.sum_Icc_one {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ x ∈ Icc 1 n, f x = ∑ k ∈ range n, f (k + 1) := by sorry
