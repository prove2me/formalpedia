-- Prove2me | Theorems.Thm_ProjLikeRetr_Spectral_eig_lipschitz
-- name    : ProjLikeRetr.Spectral.eig_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:01:55.681794+00:00
-- url     : https://prove2.me/theorems/1977efba-1f8f-40d4-ae89-c562524dc1e3
-- title:
--   (3.11), p. 12 — the sorted-eigenvalue map $\lambda : \mathbf S_n \to \mathbb R^n_\downarrow$ is 1-Lipschitz
-- statement:
--   Let $X, Y \in \mathbf S_n$ be real symmetric $n \times n$ matrices and let $\lambda(X), \lambda(Y) \in \mathbb R^n_\downarrow$ be their vectors of eigenvalues in nonincreasing order. Then
--   $$
--   \|\lambda(X) - \lambda(Y)\| \le \|X - Y\|,
--   $$
--   where the left-hand norm is the Euclidean norm on $\mathbb R^n$ and the right-hand norm is the Frobenius norm $\|Z\|^2 = \sum_{i,j} Z_{ij}^2$.
--
--   This is the Hoffman–Wielandt-type inequality the paper derives from the trace inequality $\operatorname{trace}(XY) \le \lambda(X)^\top \lambda(Y)$ (3.10). It is the first step in the proof of Lemma 3.7 and gives $\|\lambda(X) - \bar x\| \le \delta/2$ in Theorem 3.9.
--
--   **Formalization Note** Matrices carry Mathlib's Frobenius norm (`open scoped Matrix.Norms.Frobenius`); vectors are `EuclideanSpace ℝ (Fin n)`.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 12, §3.4, display (3.11)

import Mathlib
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
open scoped Matrix.Norms.Frobenius

namespace ProjLikeRetr.Spectral

/-- (3.11), p. 12: the eigenvalue map `λ : 𝐒ₙ → ℝⁿ↓` is 1-Lipschitz from the Frobenius norm
to the Euclidean norm. -/
theorem eig_lipschitz {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsHermitian)
    (hY : Y.IsHermitian) : ‖eig X - eig Y‖ ≤ ‖X - Y‖ := by sorry

end ProjLikeRetr.Spectral
