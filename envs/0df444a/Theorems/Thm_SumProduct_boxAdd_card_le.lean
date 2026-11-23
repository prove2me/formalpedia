-- Prove2me | Theorems.Thm_SumProduct_boxAdd_card_le
-- name    : SumProduct.boxAdd_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:50:58.041631+00:00
-- url     : https://prove2.me/theorems/d84f9ed4-8766-4808-bad1-8acfd241f139
-- title:
--   Sum Product: box Add card le
-- statement:
--   **Upper bound of Lemma 3.5.** `|B⁺(X)| ≤ (2X+1)^d`, by `L^∞` packing: the unit cubes centred
--   at the (1-separated) embedded lattice points are disjoint and lie in a box of side `2X+1`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L125-L184
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L125-L184

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open MeasureTheory NumberField NumberField.InfinitePlace

theorem SumProduct.boxAdd_card_le (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (d : ℕ) (hd : Module.finrank ℚ K = d) (X : ℝ) (hX : 0 ≤ X) :
    ((boxAdd K X).card : ℝ) ≤ (2 * X + 1) ^ d := by sorry
