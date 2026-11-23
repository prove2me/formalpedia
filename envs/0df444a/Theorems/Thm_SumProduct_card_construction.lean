-- Prove2me | Theorems.Thm_SumProduct_card_construction
-- name    : SumProduct.card_construction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:03:47.366304+00:00
-- url     : https://prove2.me/theorems/b3d39106-222d-4006-bf0d-7c06f03e1f8c
-- title:
--   Sum Product: card construction
-- statement:
--   The construction `A = G·(n + B)` has exactly `|G|·|B|` elements, when `B ⊆ B⁺(r)` and `r` is
--   small enough (`(n+r)/(n−r) < φ`). This is the cardinality payoff of [`directness`]: the product
--   map `(g, b) ↦ g·(n + b)` is injective on `G ×ˢ B`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Construction.lean#L161-L174
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Construction.lean#L161-L174

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_Martinet
import Definitions.Def_SumProduct_AdditiveCount
import Definitions.Def_SumProduct_MultiplicativeCount
import Definitions.Def_SumProduct_RegulatorBound
import Definitions.Def_SumProduct_Construction
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open Real

theorem SumProduct.card_construction {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {n : ℕ} {r : ℝ} (hrn : r < (n : ℝ))
    (hφ : ((n : ℝ) + r) / ((n : ℝ) - r) < goldenRatio)
    (G : Finset (𝓞 K)ˣ) (B : Finset (𝓞 K)) (hB : ∀ b ∈ B, b ∈ boxAdd K r) :
    ((G ×ˢ B).image
        (fun gb : (𝓞 K)ˣ × 𝓞 K => (gb.1 : 𝓞 K) * ((n : 𝓞 K) + gb.2))).card
      = G.card * B.card := by sorry
