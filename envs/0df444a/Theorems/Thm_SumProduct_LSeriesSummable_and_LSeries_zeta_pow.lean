-- Prove2me | Theorems.Thm_SumProduct_LSeriesSummable_and_LSeries_zeta_pow
-- name    : SumProduct.LSeriesSummable_and_LSeries_zeta_pow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:00:18.724536+00:00
-- url     : https://prove2.me/theorems/6e3fd27a-50db-4740-a54a-c6fe5decb4fe
-- title:
--   Sum Product: LSeries Summable and LSeries zeta pow
-- statement:
--   The L-series of the `d`-fold divisor function `ζ^d` is summable and equals the `d`-th power of
--   the Riemann zeta function on `1 < re s`. Induction on `d` via `LSeries_mul'`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/EulerBound.lean#L373-L407
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/EulerBound.lean#L373-L407

import Mathlib
import Definitions.Def_SumProduct_EulerBound
set_option autoImplicit true
open scoped NumberField
open NumberField UniqueFactorizationMonoid
open SumProduct
variable {K : Type*} [Field K] [NumberField K]
open scoped LSeries.notation
open ArithmeticFunction

theorem SumProduct.LSeriesSummable_and_LSeries_zeta_pow {s : ℂ} (hs : 1 < s.re) (d : ℕ) :
    LSeriesSummable (fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ d) n : ℂ)) s ∧
      LSeries (fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ d) n : ℂ)) s
        = riemannZeta s ^ d := by sorry
