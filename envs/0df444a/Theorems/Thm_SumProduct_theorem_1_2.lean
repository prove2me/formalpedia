-- Prove2me | Theorems.Thm_SumProduct_theorem_1_2
-- name    : SumProduct.theorem_1_2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:05:06.801464+00:00
-- url     : https://prove2.me/theorems/5ce2dfc5-7c1a-4105-917b-16e07a44c3ef
-- title:
--   Sum Product: theorem 1 2
-- statement:
--   **Theorem 1.2** (the general construction), in its real-embedded form.
--
--   There is an absolute constant `C > 0` such that, for infinitely many `d`, there is a totally real
--   number field `K` of degree `d`; choosing a real embedding `K ↪ ℝ` and applying the construction of
--   §4 with parameter `X ≥ 1`, the image `A ⊆ ℝ` of the constructed set `A ⊆ 𝒪_K` satisfies
--   `X^d ≤ |A| ≤ (CX)^d`, `|A + A| ≤ C^d |A|`, and `|A·A| ≤ |A|² / 2^d`.
--
--   Since a ring homomorphism out of a field is injective, the real embedding preserves the
--   cardinalities of `A`, `A + A` and `A · A`, so the bounds transfer verbatim from `𝒪_K` to `ℝ`.
--
--   In the paper this is Theorem 1.2 (with `A ⊆ 𝒪_K`); its proof combines the construction Lemma 4.1
--   with the field supplied by the explicit Martinet-towers hypothesis.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Construction.lean#L491-L624
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Construction.lean#L491-L624

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

theorem SumProduct.theorem_1_2 (hMartinet : MartinetTotallyRealTowers) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧ 2 ≤ d ∧ ∀ X : ℝ, 1 ≤ X →
      ∃ A : Finset ℝ,
        X ^ d ≤ (A.card : ℝ) ∧ (A.card : ℝ) ≤ (C * X) ^ d ∧
        ((A + A).card : ℝ) ≤ C ^ d * (A.card : ℝ) ∧
        ((A * A).card : ℝ) ≤ (A.card : ℝ) ^ 2 / 2 ^ d := by sorry
