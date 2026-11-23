-- Prove2me | Theorems.Thm_SumProduct_zeta_pow_apply_prime_pow
-- name    : SumProduct.zeta_pow_apply_prime_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:00:09.65035+00:00
-- url     : https://prove2.me/theorems/d99bbd87-d0d7-43bc-a33e-1b51be44ff72
-- title:
--   Sum Product: zeta pow apply prime pow
-- statement:
--   The `d`-fold divisor function `ζ^d` (Dirichlet convolution power) at a prime power:
--   `(ζ^d)(p^k) = C(d+k-1, k) = multichoose d k`. Proved by induction on `d`: the convolution
--   `(ζ^d * ζ)(p^k) = ∑_{i≤k} (ζ^d)(p^i)` telescopes by the hockey-stick identity for `multichoose`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/EulerBound.lean#L308-L329
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/EulerBound.lean#L308-L329

import Mathlib
import Definitions.Def_SumProduct_EulerBound
set_option autoImplicit true
open scoped NumberField
open NumberField UniqueFactorizationMonoid
open SumProduct
variable {K : Type*} [Field K] [NumberField K]
open scoped ArithmeticFunction.zeta

theorem SumProduct.zeta_pow_apply_prime_pow {p : ℕ} (hp : p.Prime) (d k : ℕ) :
    (ζ ^ d : ArithmeticFunction ℕ) (p ^ k) = Nat.multichoose d k := by sorry
