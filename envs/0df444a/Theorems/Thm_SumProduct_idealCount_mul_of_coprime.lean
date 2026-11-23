-- Prove2me | Theorems.Thm_SumProduct_idealCount_mul_of_coprime
-- name    : SumProduct.idealCount_mul_of_coprime
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:59:52.092805+00:00
-- url     : https://prove2.me/theorems/46bdd657-527a-4688-b4a1-a76138b042f7
-- title:
--   Sum Product: ideal Count mul of coprime
-- statement:
--   **Multiplicativity** of the ideal-counting function: for coprime `m, n`,
--   `a_{mn} = a_m · a_n`. The bijection is `(I, J) ↦ I·J` (norms multiply); surjectivity is
--   `exists_split`, injectivity uses that coprime norms give coprime ideals.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/EulerBound.lean#L126-L146
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/EulerBound.lean#L126-L146

import Mathlib
import Definitions.Def_SumProduct_EulerBound
set_option autoImplicit true
open scoped NumberField
open NumberField UniqueFactorizationMonoid
open SumProduct
variable {K : Type*} [Field K] [NumberField K]

theorem SumProduct.idealCount_mul_of_coprime {m n : ℕ} (hmn : Nat.Coprime m n) (hm : m ≠ 0) (hn : n ≠ 0) :
    idealCount K (m * n) = idealCount K m * idealCount K n := by sorry
