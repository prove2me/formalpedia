-- Prove2me | Theorems.Thm_SumProduct_count_encard_le
-- name    : SumProduct.count_encard_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:51:04.762694+00:00
-- url     : https://prove2.me/theorems/9d7453bd-cfee-42ff-9394-4f1a5d11e661
-- title:
--   Sum Product: count encard le
-- statement:
--   `encard` form of `count_le_boxAdd` (the form needed for the tsum bound).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L312-L345
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L312-L345

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace

theorem SumProduct.count_encard_le {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (x : mixedSpace K) (r : NNReal) :
    {α : 𝓞 K | latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)}.encard
      ≤ ((boxAdd K (2 * (r : ℝ))).card : ℕ∞) := by sorry
