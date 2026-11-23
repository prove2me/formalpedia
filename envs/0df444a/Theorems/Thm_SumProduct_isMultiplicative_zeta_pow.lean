-- Prove2me | Theorems.Thm_SumProduct_isMultiplicative_zeta_pow
-- name    : SumProduct.isMultiplicative_zeta_pow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:00:00.755805+00:00
-- url     : https://prove2.me/theorems/0d8376ec-a841-4b14-90e8-e54c402621ea
-- title:
--   Sum Product: is Multiplicative zeta pow
-- statement:
--   The Sum Product construction uses the is Multiplicative zeta pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/EulerBound.lean#L347-L351
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/EulerBound.lean#L347-L351

import Mathlib
import Definitions.Def_SumProduct_EulerBound
set_option autoImplicit true
open scoped NumberField
open NumberField UniqueFactorizationMonoid
open SumProduct
variable {K : Type*} [Field K] [NumberField K]

theorem SumProduct.isMultiplicative_zeta_pow (d : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ d).IsMultiplicative := by sorry
