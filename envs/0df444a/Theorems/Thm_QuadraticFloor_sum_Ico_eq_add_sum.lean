-- Prove2me | Theorems.Thm_QuadraticFloor_sum_Ico_eq_add_sum
-- name    : QuadraticFloor.sum_Ico_eq_add_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:56.579053+00:00
-- url     : https://prove2.me/theorems/2a7e792a-0f96-56fd-add3-6d50f9d8a2c3
-- title:
--   Quadratic Floor: sum Ico eq add sum
-- statement:
--   The Quadratic Floor construction uses the sum Ico eq add sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L28-L32
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L28-L32

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.sum_Ico_eq_add_sum (g : ℤ → ℤ) {a b : ℤ} (h : a < b) :
    ∑ j ∈ Ico a b, g j = g a + ∑ j ∈ Ico (a + 1) b, g j := by sorry
