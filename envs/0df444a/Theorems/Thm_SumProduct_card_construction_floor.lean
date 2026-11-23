-- Prove2me | Theorems.Thm_SumProduct_card_construction_floor
-- name    : SumProduct.card_construction_floor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:04:32.256211+00:00
-- url     : https://prove2.me/theorems/65c1ec3d-4526-471d-8164-8104d74e1c79
-- title:
--   Sum Product: card construction floor
-- statement:
--   The Lemma 4.1 construction `A = B^×(Y)·(⌊X⌋ + B⁺(εX))` has exactly `|B^×(Y)|·|B⁺(εX)|`
--   elements, for `X ≥ 2` and `0 < ε ≤ 3/20` (instantiating [`card_construction`] via the floor-ratio
--   bound).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Construction.lean#L180-L190
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Construction.lean#L180-L190

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

theorem SumProduct.card_construction_floor (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (Y : ℝ) {X ε : ℝ} (hX : 2 ≤ X) (hε0 : 0 < ε) (hε : ε ≤ 3 / 20) :
    ((boxMult K Y ×ˢ boxAdd K (ε * X)).image
        (fun gb : (𝓞 K)ˣ × 𝓞 K => (gb.1 : 𝓞 K) * ((⌊X⌋₊ : 𝓞 K) + gb.2))).card
      = (boxMult K Y).card * (boxAdd K (ε * X)).card := by sorry
