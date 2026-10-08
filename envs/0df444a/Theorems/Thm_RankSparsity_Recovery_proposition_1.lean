-- Prove2me | Theorems.Thm_RankSparsity_Recovery_proposition_1
-- name    : RankSparsity.Recovery.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:31.018086+00:00
-- url     : https://prove2.me/theorems/f63de5c4-3015-4037-8de3-ade1187ec0ac
-- title:
--   Proposition 1 — μ(A⋆)ξ(B⋆) < 1 implies Ω(A⋆) ∩ T(B⋆) = {0}
-- statement:
--   Throughout, $A^\star, B^\star \in \mathbb R^{n\times n}$ are real square matrices, $B^\star = U\Sigma V^{T}$ is a compact singular value decomposition with $U, V\in\mathbb R^{n\times k}$ having orthonormal columns and $k = \operatorname{rank}(B^\star)$, $\Omega = \Omega(A^\star)$ is the space of matrices supported inside $\operatorname{support}(A^\star)$, $T = T(B^\star) = \{UX^{T} + YV^{T}\}$, $\mu(A^\star)$ and $\xi(B^\star)$ are the incoherence quantities (1.2) and (1.1), $\|\cdot\|$ is the spectral norm and $\|\cdot\|_\infty$ the largest entry in magnitude.
--
--   **Proposition 1.** For any two matrices $A^\star, B^\star$,
--   $$\mu(A^\star)\,\xi(B^\star)<1\ \Longrightarrow\ \Omega(A^\star)\cap T(B^\star)=\{0\}.$$
--
--   Transversality of the two tangent spaces is the identifiability condition for the decomposition when the tangent spaces are known, and it is condition 1 of Proposition 2.
--
--   **Formalization Note** $T(B^\star)$ is built from a given compact SVD of $B^\star$; the statement holds for every such SVD.
-- source:
--   Chandrasekaran, Sanghavi, Parrilo, Willsky, Rank-Sparsity Incoherence for Matrix Decomposition, arXiv:0906.2220v1, Proposition 1, p. 7

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_RankSparsity_Recovery_Setup

open MatrixCompletion

namespace RankSparsity.Recovery

/-- Proposition 1 (p. 7): if `μ(A⋆) ξ(B⋆) < 1` then `Ω(A⋆) ∩ T(B⋆) = {0}`. -/
theorem proposition_1 {n r : ℕ} (Astar Bstar : RealMatrix n n) (S : SVD Bstar r)
    (h : mu Astar * xi S < 1) :
    ∀ N : RealMatrix n n, InOmega Astar N → InT S N → N = 0 := by sorry

end RankSparsity.Recovery
