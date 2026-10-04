-- Prove2me | Theorems.Thm_ProjLikeRetr_Spectral_lemma_3_7
-- name    : ProjLikeRetr.Spectral.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:01:47.933901+00:00
-- url     : https://prove2.me/theorems/f9b6c8e0-a2d6-4c4a-bc2e-b5b523d2655f
-- title:
--   Lemma 3.7, p. 12 — projection onto spectral sets (for sorted $z$)
-- statement:
--   Let $M$ be a closed subset of $\mathbb R^n_\downarrow$, and let $X \in \mathbf S_n$ have an eigendecomposition $X = U \operatorname{Diag}(\lambda(X)) U^\top$ with $U \in \mathbf O_n$ orthogonal. For a vector $z \in \mathbb R^n_\downarrow$,
--   $$
--   U \operatorname{Diag}(z)\, U^\top \in P_{\lambda^{-1}(M)}(X) \iff z \in P_M(\lambda(X)),
--   $$
--   where $P_Q(y)$ is the set of nearest points of $Q$ to $y$ (Frobenius norm on matrices, Euclidean norm on vectors).
--
--   The lemma reduces nearest-point problems on a spectral set of symmetric matrices to the corresponding problem on the underlying set of sorted vectors, keeping the eigenvectors of $X$. It is the final step of the proof of Theorem 3.9.
--
--   **Formalization Note** The lemma is stated for sorted $z \in \mathbb R^n_\downarrow$. As printed (for all $z \in \mathbb R^n$) the direction "$\Rightarrow$" is false: with $n = 2$, $M = \{(2,0)\}$, $X = U = I$ and $z = (0,2)$, every element of $\lambda^{-1}(M)$ is at distance $\sqrt 2$ from $I$, so $\operatorname{Diag}(0,2) \in P_{\lambda^{-1}(M)}(I)$, but $z \notin M$. The paper's proof shows only that $z$ attains the distance; for sorted $z$ one has $\lambda(U\operatorname{Diag}(z)U^\top) = z$ and the proof is complete. Theorem 3.9 uses only sorted $z$. Closedness of $M$ is kept as printed. $P_Q(y)$ is written with the platform predicate `IsMetricProjection Q y z`.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 12, Lemma 3.7 (proof p. 13, (3.16))

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
open scoped Matrix Matrix.Norms.Frobenius
open RandomGradFree.Nonsmooth

namespace ProjLikeRetr.Spectral

/-- Lemma 3.7, p. 12 (projection onto spectral sets), for nonincreasingly sorted `z`. -/
theorem lemma_3_7 {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n))) (hMsub : M ⊆ sortedDesc n)
    (hMc : IsClosed M) (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsHermitian)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (hXU : X = U * Matrix.diagonal (WithLp.ofLp (eig X)) * Uᵀ)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ sortedDesc n) :
    IsMetricProjection (specSet M) X (U * Matrix.diagonal (WithLp.ofLp z) * Uᵀ) ↔
      IsMetricProjection M (eig X) z := by sorry

end ProjLikeRetr.Spectral
