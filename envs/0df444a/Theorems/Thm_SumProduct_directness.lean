-- Prove2me | Theorems.Thm_SumProduct_directness
-- name    : SumProduct.directness
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:03:11.706913+00:00
-- url     : https://prove2.me/theorems/45203bbf-2ce4-46dd-9734-332161300ae3
-- title:
--   Sum Product: directness
-- statement:
--   **Directness of the construction** (the key step in Lemma 4.1).
--
--   If `g₁(n + b₁) = g₂(n + b₂)` with `g₁, g₂` units, `b₁, b₂ ∈ B⁺(r)`, and `r` small enough that
--   `(n+r)/(n−r) < φ`, then `g₁ = g₂` and `b₁ = b₂`. Hence the product map `G × P → 𝒪_K`,
--   `(g, p) ↦ g·p` (with `P = n + B⁺(r)`) is injective, giving `|A| = |G|·|P|`.
--
--   The unit `u = g₁⁻¹g₂` satisfies `p₁ = u·p₂`, so every archimedean absolute value of `u` is
--   `w(p₁)/w(p₂) ∈ [(n−r)/(n+r), (n+r)/(n−r)] ⊆ (φ⁻¹, φ)`; by [`unit_separation`] `u = ±1`, and `u = −1`
--   is excluded since it would force `b₁ + b₂ = −2n`, whence `2n = w(b₁+b₂) ≤ 2r < 2n`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Construction.lean#L63-L127
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Construction.lean#L63-L127

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
open Real

theorem SumProduct.directness {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {n : ℕ} {r : ℝ} (hrn : r < (n : ℝ))
    (hφ : ((n : ℝ) + r) / ((n : ℝ) - r) < goldenRatio)
    {g₁ g₂ : (𝓞 K)ˣ} {b₁ b₂ : 𝓞 K} (hb₁ : b₁ ∈ boxAdd K r) (hb₂ : b₂ ∈ boxAdd K r)
    (heq : (g₁ : 𝓞 K) * ((n : 𝓞 K) + b₁) = (g₂ : 𝓞 K) * ((n : 𝓞 K) + b₂)) :
    g₁ = g₂ ∧ b₁ = b₂ := by sorry
