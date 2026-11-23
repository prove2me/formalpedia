-- Prove2me | Theorems.Thm_SumProduct_place_construction_le
-- name    : SumProduct.place_construction_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:03:38.776569+00:00
-- url     : https://prove2.me/theorems/f358722a-5232-422c-b387-0a8aa593528e
-- title:
--   Sum Product: place construction le
-- statement:
--   Every element `g·(n + b)` of the construction (with `g ∈ B^×(Y)`, `b ∈ B⁺(r)`) has every
--   archimedean absolute value `≤ e^Y · (n + r)`: multiplication by a unit in `B^×(Y)` expands each
--   embedding by at most `e^Y`. This drives the sumset bound `A + A ⊆ B⁺(4Xe^Y)` in Lemma 4.1.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Construction.lean#L139-L154
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Construction.lean#L139-L154

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

theorem SumProduct.place_construction_le {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (w : NumberField.InfinitePlace K) {Y : ℝ} {g : (𝓞 K)ˣ} (hg : g ∈ boxMult K Y)
    {n : ℕ} {r : ℝ} {b : 𝓞 K} (hb : b ∈ boxAdd K r) :
    w (((g : 𝓞 K) * ((n : 𝓞 K) + b) : 𝓞 K) : K) ≤ Real.exp Y * ((n : ℝ) + r) := by sorry
