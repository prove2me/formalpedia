-- Prove2me | Theorems.Thm_SumProduct_mem_convexBodyLT_iff
-- name    : SumProduct.mem_convexBodyLT_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:57:14.210135+00:00
-- url     : https://prove2.me/theorems/e624b966-c575-4f9b-a631-231f20d471f8
-- title:
--   Sum Product: mem convex Body LT iff
-- statement:
--   Membership in the open box `convexBodyLT K f`, in terms of `normAtPlace`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L239-L250
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L239-L250

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Metric

theorem SumProduct.mem_convexBodyLT_iff {K : Type*} [Field K] [NumberField K] (f : InfinitePlace K → NNReal)
    (y : mixedSpace K) : y ∈ convexBodyLT K f ↔ ∀ w : InfinitePlace K, normAtPlace w y < f w := by sorry
