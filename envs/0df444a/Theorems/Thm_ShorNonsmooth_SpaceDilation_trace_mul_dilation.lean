-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_trace_mul_dilation
-- name    : ShorNonsmooth.SpaceDilation.trace_mul_dilation
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-04T01:20:56.045239+00:00
-- url     : https://prove2.me/theorems/c6ece6fe-e782-4fea-9209-f67e3ccfe313
-- title:
--   one step of the SDG recursion grows the trace of the Gram operator by $(\alpha^2-1)\|A\xi\|^2$ (Shor 1985, p. 55)
-- statement:
--   Write `S v = (ξ, v) ξ` for a unit vector `ξ`, so that `S` is the orthogonal projection onto the line `span ξ`, and observe that `dilation a ξ = I + (a-1) S`. Expanding one step of the Gram recursion gives
--
--   `R (A A) R = (A A) + (a-1) S (A A) + (a-1) (A A) S + (a-1)^2 S (A A) S`.
--
--   For an arbitrary endomorphism `P`, cyclicity of the trace gives `tr (S P) = tr (P S)`, and `S P S` has trace `⟪ξ, P ξ⟫`, because `S P S` sends `v` to `(P (v, ξ) ξ, ξ) ξ` and only the component of `v` along `ξ` contributes to the trace. Substituting `P = A A` and using that `A` is self-adjoint, so that `⟪ξ, A (A ξ)⟫ = ⟪A ξ, A ξ⟫ = ‖A ξ‖^2`, the three rank-one terms contribute `2(a-1)‖A ξ‖^2 + (a-1)^2‖A ξ‖^2`, and `2(a-1) + (a-1)^2 = a^2 - 1`.
--
--   The identity is stated for `a` and `ξ` of arbitrary sign and for any self-adjoint `A`; only `‖ξ‖ = 1` is used. It is the trace-growth line on p. 55 of the book and, combined with `det (dilation a ξ) = a` and the arithmetic-geometric mean inequality for the positive eigenvalues of `A k A k`, it yields Theorem 3.2.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 55, proof of Theorem 3.2

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

namespace ShorNonsmooth.SpaceDilation

/-- **The trace identity of Shor (1985), p. 55.** For a self-adjoint continuous linear
operator `A` on `E n`, a unit vector `ξ` and any `a : ℝ`,

`tr (R ∘ (A A) ∘ R) = tr (A A) + (a^2 - 1) * ‖A ξ‖^2`,  R = dilation a ξ.

Indeed `dilation a ξ = id + (a-1) S` with `S v = (ξ, v) ξ` the orthogonal projection onto
`span ξ`, and for every endomorphism `P`
`tr (S ∘ₗ P) = tr (P ∘ₗ S) = tr (S ∘ₗ P ∘ₗ S) = ⟪ξ, P ξ⟫`, so expanding
`R (A A) R = (A A) + (a-1) S (A A) + (a-1) (A A) S + (a-1)^2 S (A A) S` and using
`⟪ξ, A (A ξ)⟫ = ‖A ξ‖^2` for self-adjoint `A` gives the factor
`2(a-1) + (a-1)^2 = a^2 - 1`. This is the only analytic input to Theorem 3.2. -/
theorem trace_mul_dilation {n : ℕ} (a : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖ = 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : A.adjoint = A) :
    ((A.toLinearMap ∘ₗ A.toLinearMap).comp ((dilation a ξ).toLinearMap)).trace ℝ _ =
      (A.toLinearMap ∘ₗ A.toLinearMap).trace ℝ _ + (a ^ 2 - 1) * ‖A ξ‖ ^ 2 := by
  sorry

end ShorNonsmooth.SpaceDilation
