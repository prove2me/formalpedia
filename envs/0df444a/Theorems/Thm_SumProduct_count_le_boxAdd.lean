-- Prove2me | Theorems.Thm_SumProduct_count_le_boxAdd
-- name    : SumProduct.count_le_boxAdd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:52:00.851392+00:00
-- url     : https://prove2.me/theorems/451e4707-9685-4862-8050-b6e7ffe128ce
-- title:
--   Sum Product: count le box Add
-- statement:
--   Pointwise count bound (heart of the Blichfeldt lower bound): for any translate by
--   `x : mixedSpace K`, the integers `α` whose embedding lands in the radius-`r` box `x + S`
--   inject (via `α ↦ α − α₀`) into `B⁺(2r)`, so there are at most `|B⁺(2r)|` of them.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L274-L308
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L274-L308

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace

theorem SumProduct.count_le_boxAdd {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (x : mixedSpace K) (r : NNReal) :
    {α : 𝓞 K | latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)}.ncard
      ≤ (boxAdd K (2 * (r : ℝ))).card := by sorry
