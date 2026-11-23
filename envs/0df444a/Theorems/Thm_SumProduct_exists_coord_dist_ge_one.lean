-- Prove2me | Theorems.Thm_SumProduct_exists_coord_dist_ge_one
-- name    : SumProduct.exists_coord_dist_ge_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:56:44.752953+00:00
-- url     : https://prove2.me/theorems/292e7510-7acb-402b-81a7-b533f24916ef
-- title:
--   Sum Product: exists coord dist ge one
-- statement:
--   Distinct algebraic integers are `1`-separated in the sup-metric of the real embedding: some
--   coordinate differs by `≥ 1`. This is the geometric form of `exists_place_ge_one`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L66-L75
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L66-L75

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.InfinitePlace

theorem SumProduct.exists_coord_dist_ge_one {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {α β : 𝓞 K} (h : α ≠ β) :
    ∃ w : InfinitePlace K, 1 ≤ |realEmbed K α w - realEmbed K β w| := by sorry
