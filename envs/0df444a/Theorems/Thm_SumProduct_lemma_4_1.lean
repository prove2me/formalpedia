-- Prove2me | Theorems.Thm_SumProduct_lemma_4_1
-- name    : SumProduct.lemma_4_1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:05:33.861123+00:00
-- url     : https://prove2.me/theorems/82aed4b5-ad66-4c12-93bd-72e4146a0bca
-- title:
--   Sum Product: lemma 4 1
-- statement:
--   **Lemma 4.1** (the construction), as stated in §4 of the paper.
--
--   There is an absolute constant `c > 0` such that for every totally real number field `K` of degree
--   `d ≥ 2` and all `X, Y ≥ 2`, there is a finite set `A ⊆ 𝒪_K` with
--   * `(cXY)^d / (Y · Δ_K^{3/2}) ≤ |A| ≤ (XY/c)^d`,
--   * `|A·A| ≤ c^{-d} Y^{1-d} Δ_K² |A|²`, and
--   * `|A + A| ≤ (e^Y/c)^d Δ_K^{1/2} |A|`,
--
--   where `Δ_K = |discr K|`.  (Here `A := G·P` with `G = B^×(Y)` a box in the unit lattice and
--   `P = X + B⁺(εX)` a box in the additive lattice; see §3–§4.)
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Construction.lean#L303-L462
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Construction.lean#L303-L462

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

theorem SumProduct.lemma_4_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
      (d : ℕ), Module.finrank ℚ K = d → 2 ≤ d → ∀ X Y : ℝ, 2 ≤ X → 2 ≤ Y →
      ∃ A : Finset (𝓞 K),
        (c * X * Y) ^ d / (Y * |(NumberField.discr K : ℝ)| ^ ((3 : ℝ) / 2)) ≤ (A.card : ℝ) ∧
        (A.card : ℝ) ≤ (X * Y / c) ^ d ∧
        ((A * A).card : ℝ) ≤
          c ^ (-(d : ℤ)) * Y ^ (1 - (d : ℤ)) * |(NumberField.discr K : ℝ)| ^ 2 * (A.card : ℝ) ^ 2 ∧
        ((A + A).card : ℝ) ≤
          (Real.exp Y / c) ^ d * |(NumberField.discr K : ℝ)| ^ ((1 : ℝ) / 2) * (A.card : ℝ) := by sorry
