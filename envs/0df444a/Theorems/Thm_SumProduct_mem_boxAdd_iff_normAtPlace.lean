-- Prove2me | Theorems.Thm_SumProduct_mem_boxAdd_iff_normAtPlace
-- name    : SumProduct.mem_boxAdd_iff_normAtPlace
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:49:00.600962+00:00
-- url     : https://prove2.me/theorems/038030bc-ae1f-4c30-a219-5b0dd4b839c0
-- title:
--   Sum Product: mem box Add iff norm At Place
-- statement:
--   `B⁺(X)` is the pullback under the mixed embedding of the box `{x : ∀ w, normAtPlace w x ≤ X}`
--   in `mixedSpace K`. This connects `boxAdd` to Mathlib's `integerLattice` (whose covolume is
--   `√|Δ_K|`), the route for the Lemma 3.5 lower bound.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Boxes.lean#L49-L51
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Boxes.lean#L49-L51

import Mathlib
import Definitions.Def_SumProduct_Boxes
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace

theorem SumProduct.mem_boxAdd_iff_normAtPlace {K : Type*} [Field K] [NumberField K] {X : ℝ} {α : 𝓞 K} :
    α ∈ boxAdd K X ↔ ∀ w : InfinitePlace K, normAtPlace w (mixedEmbedding K (α : K)) ≤ X := by sorry
