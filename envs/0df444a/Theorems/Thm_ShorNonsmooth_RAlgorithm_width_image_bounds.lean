-- Prove2me | Theorems.Thm_ShorNonsmooth_RAlgorithm_width_image_bounds
-- name    : ShorNonsmooth.RAlgorithm.width_image_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T16:13:17.62621+00:00
-- url     : https://prove2.me/theorems/1b13202b-591f-43af-9234-1a38941749fb
-- title:
--   Lemma 3.2 — the width of $BW$ lies between $\lambda(B)\,d(W)$ and $\lambda(B)\,D(W)$
-- statement:
--   Let $W$ be a convex, closed and bounded body in $E_n$ ($n \ge 1$), with width $d(W)$ and diameter $D(W)$. Let $B$ be a linear operator with a polar decomposition $B = SO$, where $O$ is an orthogonal operator and $S$ is a symmetric nonnegative definite operator whose minimum eigenvalue is $\lambda(B)$. Then the width of the image $BW$ satisfies
--   $$
--   \lambda(B)\, d(W) \le d(BW) \le \lambda(B)\, D(W).
--   $$
--
--   The lemma controls how a linear change of variables can thin out a convex body: the width can shrink at most by the factor $\lambda(B)$, and it does shrink to at most $\lambda(B)$ times the diameter.
--
--   **Formalization Note** "Body" is taken to mean nonempty interior. $O$ is a linear isometry equivalence of $E_n$, $S$ a positive (self-adjoint, nonnegative) continuous linear operator, and $\lambda(B)$ an eigenvalue of $S$ that is at most every eigenvalue of $S$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 80, Lemma 3.2

import Mathlib
import Definitions.Def_ShorNonsmooth_RAlgorithm_Widths

open scoped InnerProductSpace

namespace ShorNonsmooth.RAlgorithm

/-- Shor (1985), p. 80, **Lemma 3.2**. Let `W` be a convex, closed and bounded body in `E_n`
(nonempty interior) and let `B = S O` be a polar decomposition of the linear operator `B`, with
`O` orthogonal and `S` symmetric nonnegative definite with minimum eigenvalue `λ(B)`. Then
`λ(B) d(W) ≤ d(BW) ≤ λ(B) D(W)`. -/
theorem width_image_bounds {n : ℕ} (hn : 0 < n) (W : Set (EuclideanSpace ℝ (Fin n)))
    (hW_convex : Convex ℝ W) (hW_closed : IsClosed W) (hW_bdd : Bornology.IsBounded W)
    (hW_body : (interior W).Nonempty)
    (B S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (O : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (hS : S.IsPositive) (hB : B = S.comp O.toContinuousLinearEquiv.toContinuousLinearMap)
    (lam : ℝ) (hlam : Module.End.HasEigenvalue (S : Module.End ℝ (EuclideanSpace ℝ (Fin n))) lam)
    (hlam_min : ∀ μ : ℝ,
      Module.End.HasEigenvalue (S : Module.End ℝ (EuclideanSpace ℝ (Fin n))) μ → lam ≤ μ) :
    lam * width W ≤ width (B '' W) ∧ width (B '' W) ≤ lam * diameterW W := by sorry

end ShorNonsmooth.RAlgorithm
