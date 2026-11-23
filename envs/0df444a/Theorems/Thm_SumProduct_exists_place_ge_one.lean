-- Prove2me | Theorems.Thm_SumProduct_exists_place_ge_one
-- name    : SumProduct.exists_place_ge_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:50:43.601404+00:00
-- url     : https://prove2.me/theorems/8169f614-bd97-4368-8c22-47958a62d2f9
-- title:
--   Sum Product: exists place ge one
-- statement:
--   A nonzero algebraic integer has some archimedean absolute value `≥ 1`: since `|N(γ)| ≥ 1` and
--   `∏_w (w γ)^{mult w} = |N(γ)|`, not all places can be `< 1`. This is the `1`-separation of distinct
--   lattice points (`α ≠ β ⟹ ∃ w, 1 ≤ w(α−β)`) underlying the upper bounds of Lemmas 3.5 and 3.7.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L25-L48
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L25-L48

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.InfinitePlace

theorem SumProduct.exists_place_ge_one {K : Type*} [Field K] [NumberField K] {γ : 𝓞 K} (hγ : γ ≠ 0) :
    ∃ w : InfinitePlace K, 1 ≤ w (γ : K) := by sorry
