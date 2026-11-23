-- Prove2me | Theorems.Thm_SumProduct_idealCount_prime_pow_le
-- name    : SumProduct.idealCount_prime_pow_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:00:02.106005+00:00
-- url     : https://prove2.me/theorems/83254be9-40e5-4714-8e04-23b2d50eb1ad
-- title:
--   Sum Product: ideal Count prime pow le
-- statement:
--   **Local bound** (step 2): the number of ideals of norm `p^k` is at most the `d`-fold divisor
--   value `d_d(p^k) = C(d+k-1, k)` (`d = [K:ℚ]`). Each such ideal factors uniquely into primes over `p`
--   (at most `d` of them, `card_primesOverFinset_le_finrank`); recording, for each prime `𝔭` over `p`,
--   the product `v_𝔭(I)·f_𝔭` of its multiplicity and inertia degree gives an injection into the
--   `finsuppAntidiag` of total `k` (the norm gives `∑ v_𝔭 f_𝔭 = k`), counted by `multichoose`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/EulerBound.lean#L187-L302
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/EulerBound.lean#L187-L302

import Mathlib
import Definitions.Def_SumProduct_EulerBound
set_option autoImplicit true
open scoped NumberField
open NumberField UniqueFactorizationMonoid
open SumProduct
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000

theorem SumProduct.idealCount_prime_pow_le {K : Type*} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    (k : ℕ) :
    idealCount K (p ^ k) ≤ Nat.multichoose (Module.finrank ℚ K) k := by sorry
