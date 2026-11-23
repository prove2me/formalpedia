-- Prove2me | Theorems.Thm_SumProduct_boxAdd_card_ge
-- name    : SumProduct.boxAdd_card_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:51:14.753422+00:00
-- url     : https://prove2.me/theorems/240bf38f-846d-4fa5-9ca5-f1d68cc53904
-- title:
--   Sum Product: box Add card ge
-- statement:
--   **Lower bound of Lemma 3.5** (Blichfeldt). For a totally real field of degree `d` and `X ≥ 0`,
--   `X^d / √Δ_K ≤ |B⁺(X)|`. Proof: the multiplicity `g(y) = #{ℓ ∈ L : ℓ + y ∈ S}` of the radius-`X/2`
--   box `S` satisfies `∫_F g = vol S = X^d` (fundamental-domain decomposition) and `g(y) ≤ |B⁺(X)|`
--   pointwise (`count`), so `X^d ≤ |B⁺(X)| · vol F = |B⁺(X)| · √Δ_K`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L375-L444
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L375-L444

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open MeasureTheory NumberField NumberField.mixedEmbedding NumberField.InfinitePlace

theorem SumProduct.boxAdd_card_ge {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {d : ℕ} (hd : Module.finrank ℚ K = d) (X : ℝ) (hX : 0 ≤ X) :
    X ^ d / Real.sqrt |(NumberField.discr K : ℝ)| ≤ (boxAdd K X).card := by sorry
