-- Prove2me | Theorems.Thm_RankSparsity_Recovery_proposition_2
-- name    : RankSparsity.Recovery.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:32.239757+00:00
-- url     : https://prove2.me/theorems/4be29f38-3cf7-45fc-9427-88277041ed99
-- title:
--   Proposition 2 — transversality plus a strict dual certificate give unique recovery
-- statement:
--   Throughout, $A^\star, B^\star \in \mathbb R^{n\times n}$ are real square matrices, $B^\star = U\Sigma V^{T}$ is a compact singular value decomposition with $U, V\in\mathbb R^{n\times k}$ having orthonormal columns and $k = \operatorname{rank}(B^\star)$, $\Omega = \Omega(A^\star)$ is the space of matrices supported inside $\operatorname{support}(A^\star)$, $T = T(B^\star) = \{UX^{T} + YV^{T}\}$, $\mu(A^\star)$ and $\xi(B^\star)$ are the incoherence quantities (1.2) and (1.1), $\|\cdot\|$ is the spectral norm and $\|\cdot\|_\infty$ the largest entry in magnitude.
--
--   **Proposition 2.** Let $C=A^\star+B^\star$. Then $(\hat A,\hat B)=(A^\star,B^\star)$ is the unique optimizer of (1.3) if:
--
--   1. $\Omega(A^\star)\cap T(B^\star)=\{0\}$, and
--   2. there exists a dual $Q\in\mathbb R^{n\times n}$ with
--   $$P_{T(B^\star)}(Q)=UV^{T},\quad P_{\Omega(A^\star)}(Q)=\gamma\operatorname{sign}(A^\star),\quad \|P_{T(B^\star)^\perp}(Q)\|<1,\quad \|P_{\Omega(A^\star)^c}(Q)\|_\infty<\gamma.$$
--
--   This is the deterministic certificate that Theorem 2 constructs.
--
--   **Formalization Note** "Unique optimizer" means: $A^\star+B^\star=C$ and every feasible pair $(A,B)\neq(A^\star,B^\star)$ has strictly larger objective $\gamma\|A\|_1+\|B\|_*$. No sign condition on $\gamma$ is assumed, as on the page.
-- source:
--   Chandrasekaran, Sanghavi, Parrilo, Willsky, Rank-Sparsity Incoherence for Matrix Decomposition, arXiv:0906.2220v1, Proposition 2, pp. 9–10

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_RankSparsity_Recovery_Setup

open MatrixCompletion

namespace RankSparsity.Recovery

/-- Proposition 2 (pp. 9–10): transversality plus a strict dual certificate `Q`
make `(A⋆, B⋆)` the unique optimizer of (1.3). -/
theorem proposition_2 {n r : ℕ} (γ : ℝ) (Astar Bstar : RealMatrix n n) (S : SVD Bstar r)
    (h1 : ∀ N : RealMatrix n n, InOmega Astar N → InT S N → N = 0)
    (h2 : ∃ Q : RealMatrix n n,
      tangentProjection S Q = signMatrix S ∧
        projOmega Astar Q = γ • entrySign Astar ∧
          spectralNorm (normalProjection S Q) < 1 ∧
            entrySupNorm (projOmegaC Astar Q) < γ) :
    IsUniqueOptimum γ (Astar + Bstar) Astar Bstar := by sorry

end RankSparsity.Recovery
