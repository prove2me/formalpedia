-- Prove2me | Theorems.Thm_ProjLikeRetr_Spectral_projection_spectral_manifold
-- name    : ProjLikeRetr.Spectral.projection_spectral_manifold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:02:44.479698+00:00
-- url     : https://prove2.me/theorems/ad29e00f-0265-4d64-8c21-9a82d1979647
-- title:
--   Theorem 3.9, p. 14 — near a locally symmetric point, $P_{\mathcal S}(X) = U \operatorname{Diag}(P_{\mathcal M}(\lambda(X)))U^\top$
-- statement:
--   Assume the hypotheses of Theorem 3.5: $\mathcal M$ is a $C^2$ submanifold of $\mathbb R^n$ of some dimension $d$; $\mathcal S = \lambda^{-1}(\mathcal M \cap \mathbb R^n_\downarrow) \subseteq \mathbf S_n$ is the associated spectral set; $\bar X \in \mathcal S$ and $\bar x = \lambda(\bar X)$; and there is $\delta > 0$ such that $\mathcal M \cap B(\bar x, \delta)$ is strongly locally symmetric (3.15).
--
--   Then, after restricting $\delta$ if necessary, there is $\delta_0 \in (0, \delta]$ such that for every symmetric matrix $X$ with $\|X - \bar X\| \le \delta_0/2$:
--
--   1. the projection of $\lambda(X)$ onto $\mathcal M$ is unique, $P_{\mathcal M}(\lambda(X)) = \{p\}$; and
--   2. for every $U \in \mathbf O_n$ with $X = U \operatorname{Diag}(\lambda(X)) U^\top$, the projection of $X$ onto $\mathcal S$ is unique and equals
--   $$
--   P_{\mathcal S}(X) = U \operatorname{Diag}\big(P_{\mathcal M}(\lambda(X))\big)\, U^\top = \{\, U \operatorname{Diag}(p)\, U^\top \,\}.
--   $$
--
--   Norms are Frobenius on matrices and Euclidean on vectors, and $P_Q(y)$ is the set of nearest points of $Q$ to $y$. The theorem gives the projective retraction on a spectral manifold in closed form: an eigendecomposition of $X$ plus a projection in $\mathbb R^n$ onto the much smaller manifold $\mathcal M$.
--
--   **Formalization Note** The page writes $P_{\mathcal S}$ and $P_{\mathcal M}$ as functions; here both are sets (nearest points, `IsMetricProjection`) and their being singletons is part of the conclusion. The radius is a $\delta_0 \le \delta$ because the proof "restrict[s] $\delta$ if necessary" so that Lemma 3.1 (local uniqueness of $P_{\mathcal M}$) and Lemma 3.8 apply; shrinking $\delta$ keeps (3.15) true. The page states Theorem 3.5 for $k = 2$ or $\infty$; $k = 2$ covers both, since a $C^\infty$ submanifold is $C^2$. The proof's "Let $X \in \lambda^{-1}(\mathcal M) \cap B(\bar X, \delta/2)$" means any symmetric $X$ in the ball, as stated here. Theorem 3.5's conclusion ($\mathcal S$ is a manifold) is not assumed.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 14, Theorem 3.9 (hypotheses: p. 12, Theorem 3.5, (3.15); proof pp. 14–15)

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_ProjLikeRetr_Spectral_IsSubmanifold
open scoped Matrix Matrix.Norms.Frobenius
open RandomGradFree.Nonsmooth

namespace ProjLikeRetr.Spectral

/-- Theorem 3.9, p. 14 (projection onto spectral manifolds), under the hypotheses of
Theorem 3.5, p. 12. -/
theorem projection_spectral_manifold {n d : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (hM : IsSubmanifold 2 d M) (Xbar : Matrix (Fin n) (Fin n) ℝ)
    (hXbar : Xbar ∈ specSet (M ∩ sortedDesc n)) (δ : ℝ) (hδ : 0 < δ)
    (hsym : IsStronglyLocallySymmetric M (eig Xbar) δ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ δ ∧ ∀ X : Matrix (Fin n) (Fin n) ℝ, X.IsHermitian →
      ‖X - Xbar‖ ≤ δ₀ / 2 →
      ∃ p : EuclideanSpace ℝ (Fin n), {z | IsMetricProjection M (eig X) z} = {p} ∧
        ∀ U ∈ Matrix.orthogonalGroup (Fin n) ℝ,
          X = U * Matrix.diagonal (WithLp.ofLp (eig X)) * Uᵀ →
          {Y | IsMetricProjection (specSet (M ∩ sortedDesc n)) X Y} =
            {U * Matrix.diagonal (WithLp.ofLp p) * Uᵀ} := by sorry

end ProjLikeRetr.Spectral
