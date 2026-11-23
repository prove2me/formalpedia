-- Prove2me | Theorems.Thm_SumProduct_realEmbed_injective
-- name    : SumProduct.realEmbed_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:51:42.70254+00:00
-- url     : https://prove2.me/theorems/4ec62baf-6bcd-4c29-a810-83f563f471a8
-- title:
--   Sum Product: real Embed injective
-- statement:
--   The Minkowski real embedding is injective (distinct integers differ in some coordinate).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L78-L84
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L78-L84

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct

theorem SumProduct.realEmbed_injective {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K] :
    Function.Injective (realEmbed K) := by sorry
