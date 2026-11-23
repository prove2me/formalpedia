-- Prove2me | Theorems.Thm_SumProduct_idealCount_one
-- name    : SumProduct.idealCount_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:00:00.07634+00:00
-- url     : https://prove2.me/theorems/0c9b7dae-17f0-4dc3-bb45-9b0949c80e14
-- title:
--   Sum Product: ideal Count one
-- statement:
--   `a_1 = 1`: the only ideal of norm `1` is `⊤`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/EulerBound.lean#L38-L44
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/EulerBound.lean#L38-L44

import Mathlib
import Definitions.Def_SumProduct_EulerBound
set_option autoImplicit true
open scoped NumberField
open NumberField UniqueFactorizationMonoid
open SumProduct
variable {K : Type*} [Field K] [NumberField K]

theorem SumProduct.idealCount_one : idealCount K 1 = 1 := by sorry
