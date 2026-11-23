-- Prove2me | Theorems.Thm_SumProduct_place_translate_bound
-- name    : SumProduct.place_translate_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:43:14.511186+00:00
-- url     : https://prove2.me/theorems/273d6093-7cfa-440f-9781-ddfbaa4c2deb
-- title:
--   Sum Product: place translate bound
-- statement:
--   Elements of the translated box `n + B⁺(r)` have every archimedean absolute value in
--   `[n - r, n + r]`. This is the additive-box geometry behind both the directness of `A = G·P`
--   and the sumset bound in Lemma 4.1.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Construction.lean#L35-L51
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Construction.lean#L35-L51

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

theorem SumProduct.place_translate_bound {K : Type*} [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) (n : ℕ) {r : ℝ} {b : 𝓞 K} (hb : b ∈ boxAdd K r) :
    (n : ℝ) - r ≤ w (((n : 𝓞 K) + b : 𝓞 K) : K) ∧
      w (((n : 𝓞 K) + b : 𝓞 K) : K) ≤ (n : ℝ) + r := by sorry
