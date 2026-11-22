-- Prove2me | Theorems.Thm_SumProduct_idealCountArith_apply_ne
-- name    : SumProduct.idealCountArith_apply_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:47:14.695456+00:00
-- url     : https://prove2.me/theorems/43a438f4-caff-49db-84d0-f0b213f99089
-- title:
--   Sum Product: ideal Count Arith apply ne
-- statement:
--   The Sum Product construction uses the ideal Count Arith apply ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/EulerBound.lean#L337-L338
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/EulerBound.lean#L337-L338

import Mathlib
import Definitions.Def_SumProduct_EulerBound
set_option autoImplicit true
open scoped NumberField
open NumberField UniqueFactorizationMonoid
open SumProduct
variable {K : Type*} [Field K] [NumberField K]

theorem SumProduct.idealCountArith_apply_ne {K : Type*} [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) :
    idealCountArith K n = idealCount K n := by sorry
