-- Prove2me | Theorems.Thm_ShorNonsmooth_AlmostDiff_convex_ae_continuously_differentiable
-- name    : ShorNonsmooth.AlmostDiff.convex_ae_continuously_differentiable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T15:56:47.646834+00:00
-- url     : https://prove2.me/theorems/760a48c4-7a98-492a-9910-419c5de64f48
-- title:
--   Proof of Theorem 1.15 (p. 18) — a convex function is almost everywhere continuously differentiable
-- statement:
--   Let $f : E_n \to \mathbb{R}$ be convex. Then
--
--   1. $f$ is differentiable at almost every point of $E_n$ (Lebesgue measure), and
--   2. the gradient $\nabla f$ is continuous on the set $M = \{x : f \text{ is differentiable at } x\}$.
--
--   The book cites this as "Rademeister's theorem [12]" (Rademacher). Together the two parts give conditions (b) and (c) of almost differentiability for convex functions; part 2 is the classical fact that the gradient of a convex function is continuous where it exists.
--
--   **Formalization Note** "Almost everywhere continuously differentiable" is read as the conjunction of a.e. differentiability and continuity of the gradient restricted to the set of points of differentiability, which is how the proof uses it.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 18, proof of Theorem 1.15, first sentence

import Mathlib

namespace ShorNonsmooth.AlmostDiff

/-- Shor (1985), p. 18, proof of Theorem 1.15, first sentence (Rademacher's theorem, cited from
[12]): a convex function on `E_n` is almost everywhere continuously differentiable, i.e. it is
differentiable at almost every point (Lebesgue measure), and its gradient is continuous on the set
of points where it is differentiable. -/
theorem convex_ae_continuously_differentiable {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))),
        DifferentiableAt ℝ f x) ∧
      ContinuousOn (gradient f) {x | DifferentiableAt ℝ f x} := by sorry

end ShorNonsmooth.AlmostDiff
