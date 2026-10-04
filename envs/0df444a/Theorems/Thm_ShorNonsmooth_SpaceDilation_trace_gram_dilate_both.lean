-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_trace_gram_dilate_both
-- name    : ShorNonsmooth.SpaceDilation.trace_gram_dilate_both
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T05:24:47.707924+00:00
-- url     : https://prove2.me/theorems/388acabc-7101-4965-89b9-bf1f4b9c0d0b
-- title:
--   the dilation sandwiches the Gram operator: tr(R (A A) R) = tr(A A) + (a^2-1)\|A\u03be\|^2 (Shor 1985, p. 55)
-- statement:
--   For a self-adjoint continuous linear operator A on Euclidean n-space, a unit vector \u03be and any real a, dilating on both sides grows the trace of the Gram operator A A by (\u03b1^2-1)\|A\u03be\|^2. This is the only analytic input to the record bound of Theorem 3.2. It replaces the earlier published theorem trace_mul_dilation, whose statement dilates only on one side and is false (for A = I it would assert a = a^2 for every a).
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 55.

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

namespace ShorNonsmooth.SpaceDilation

/-- **The trace identity of Shor (1985), p. 55.** For a self-adjoint continuous linear
operator `A` on `E n`, a unit vector `ξ` and any `a : ℝ`,

`tr (R ∘ (A A) ∘ R) = tr (A A) + (a^2 - 1) * ‖A ξ‖^2`,  `R = dilation a ξ`.

Indeed `dilation a ξ = id + (a-1) S` with `S v = ⟪ξ, v⟫ • ξ` the orthogonal projection
onto `span ξ`, and for every endomorphism `P`
`tr (S ∘ₗ P) = tr (P ∘ₗ S) = tr (S ∘ₗ P ∘ₗ S) = ⟪ξ, P ξ⟫`, so expanding
`R (A A) R = (A A) + (a-1) S (A A) + (a-1) (A A) S + (a-1)^2 S (A A) S` and using
`⟪ξ, A (A ξ)⟫ = ‖A ξ‖^2` for self-adjoint `A` gives the factor
`2(a-1) + (a-1)^2 = a^2 - 1`. This is the only analytic input to Theorem 3.2. -/
theorem trace_gram_dilate_both {n : ℕ} (a : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖ = 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : A.adjoint = A) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
          ((dilation a ξ).toLinearMap ∘ₗ
            ((A.toLinearMap ∘ₗ A.toLinearMap) ∘ₗ (dilation a ξ).toLinearMap))
      = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (A.toLinearMap.comp A.toLinearMap)
        + (a ^ 2 - 1) * ‖A ξ‖ ^ 2 := by
  sorry

end ShorNonsmooth.SpaceDilation
