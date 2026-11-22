-- Prove2me | Theorems.Thm_SumProduct_abs_realEmbed
-- name    : SumProduct.abs_realEmbed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:49:16.118364+00:00
-- url     : https://prove2.me/theorems/6d3fe20b-7949-4a07-a6f8-06b843d1c0c2
-- title:
--   Sum Product: abs real Embed
-- statement:
--   Each coordinate of `realEmbed` has absolute value equal to the corresponding place.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L59-L61
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L59-L61

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.InfinitePlace

theorem SumProduct.abs_realEmbed {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (α : 𝓞 K) (w : InfinitePlace K) : |realEmbed K α w| = w (α : K) := by sorry
