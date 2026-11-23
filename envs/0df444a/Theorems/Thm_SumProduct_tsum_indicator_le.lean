-- Prove2me | Theorems.Thm_SumProduct_tsum_indicator_le
-- name    : SumProduct.tsum_indicator_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:51:21.074712+00:00
-- url     : https://prove2.me/theorems/3bf8e39a-ed23-4cb6-9ce1-0610be2c33eb
-- title:
--   Sum Product: tsum indicator le
-- statement:
--   The multiplicity at `x`: the number of lattice points `ℓ` with `ℓ + x` in the radius-`r` box
--   is at most `|B⁺(2r)|`. (Tsum form of `count_encard_le`, reindexed over `𝒪_K`.)
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L350-L367
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L350-L367

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace

theorem SumProduct.tsum_indicator_le {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (x : mixedSpace K) (r : NNReal) :
    ∑' l : ↥(mixedEmbedding.integerLattice K),
        (convexBodyLT K (fun _ => r)).indicator (fun _ => (1 : ENNReal)) ((l : mixedSpace K) + x)
      ≤ ((boxAdd K (2 * (r : ℝ))).card : ENNReal) := by sorry
