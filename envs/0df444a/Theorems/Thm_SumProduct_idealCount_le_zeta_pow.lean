-- Prove2me | Theorems.Thm_SumProduct_idealCount_le_zeta_pow
-- name    : SumProduct.idealCount_le_zeta_pow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:59:57.781571+00:00
-- url     : https://prove2.me/theorems/9e35edc1-add6-40be-8ec7-7438fdf3b44a
-- title:
--   Sum Product: ideal Count le zeta pow
-- statement:
--   **Step 3**: the pointwise divisor bound `a_n ≤ d_d(n)` for `n ≥ 1`. Both `a` and the `d`-fold
--   divisor `ζ^d` are multiplicative, so the bound reduces (`multiplicative_factorization`) to the prime
--   powers, where it is `idealCount_prime_pow_le` together with `zeta_pow_apply_prime_pow`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/EulerBound.lean#L356-L367
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/EulerBound.lean#L356-L367

import Mathlib
import Definitions.Def_SumProduct_EulerBound
set_option autoImplicit true
open scoped NumberField
open NumberField UniqueFactorizationMonoid
open SumProduct
variable {K : Type*} [Field K] [NumberField K]

theorem SumProduct.idealCount_le_zeta_pow {K : Type*} [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) :
    idealCount K n
      ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (Module.finrank ℚ K)) n := by sorry
