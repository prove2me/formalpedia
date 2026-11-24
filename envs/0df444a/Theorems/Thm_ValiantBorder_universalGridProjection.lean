-- Prove2me | Theorems.Thm_ValiantBorder_universalGridProjection
-- name    : ValiantBorder.universalGridProjection
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:03:44.28094+00:00
-- url     : https://prove2.me/theorems/2f080743-68d2-49d0-9853-6842b3ddc4d1
-- title:
--   Affine grid projection of the universal sum evaluator
-- statement:
--   Given finitely supported program weights, a grid-complete family can realize the universal plain sum by affine substitutions on one-hot word variables. For sufficiently large input and family sizes, the substitutions work uniformly on all promised inputs, over every coefficient field containing an image of the weight ring.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Circuit.lean).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Circuit.lean.

import Definitions.Def_ValiantBorder_programWord
import Definitions.Def_ValiantBorder_gridComplete

open NS1 MvPolynomial

theorem ValiantBorder.universalGridProjection {A : Type} [CommRing A] {θ : List Bool → A} (hθ : (Function.support θ).Finite) {H : ℕ} (hH : 32 ≤ H) (κ : ℕ) :
    ∃ B₀ v₀ : ℕ, 0 < B₀ ∧ ∀ (F : Type) [Field F] [Algebra A F] (G : ∀ S, MvPolynomial (Fin S × Fin S) F),
      ValiantBorder.GridComplete F G κ → ∀ v m, v₀ ≤ v → v ^ B₀ ≤ m →
      ∃ Mat : Fin m × Fin m → MvPolynomial (Fin (v ^ (H - 32) + 1) × Option Bool) F,
        (∀ q, ValiantBorder.IsAffine (Mat q)) ∧ (aeval Mat (G m)).totalDegree ≤ v ^ (H - 32) + 1 ∧
        ∀ z : Tree, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z →
          eval (codeB F (v ^ (H - 32) + 1) (tbits z)) (aeval Mat (G m)) = algebraMap A F (pv θ z) := by sorry
