-- Prove2me | Theorems.Thm_SumProduct_card_le_boxAdd_of_ball
-- name    : SumProduct.card_le_boxAdd_of_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:52:07.505866+00:00
-- url     : https://prove2.me/theorems/e3fb0cb5-b9c5-48ff-b0d8-5051019e4314
-- title:
--   Sum Product: card le box Add of ball
-- statement:
--   Difference-set step of the Lemma 3.5 lower bound: any finite set of integers whose embeddings
--   all lie in a sup-ball of radius `r` around a common centre injects (via `α ↦ α − α₀`) into
--   `B⁺(2r)`, so its cardinality is `≤ |B⁺(2r)|`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L190-L217
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L190-L217

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.InfinitePlace

theorem SumProduct.card_le_boxAdd_of_ball {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (r : ℝ) (c : InfinitePlace K → ℝ) (T : Finset (𝓞 K))
    (hT : ∀ α ∈ T, ∀ w, |realEmbed K α w - c w| ≤ r) :
    T.card ≤ (boxAdd K (2 * r)).card := by sorry
