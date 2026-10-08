-- Prove2me | Theorems.Thm_RankSparsity_Recovery_tangentProjection_le_two
-- name    : RankSparsity.Recovery.tangentProjection_le_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:37.273621+00:00
-- url     : https://prove2.me/theorems/83a45976-c2ce-4356-a0a6-b5064cd3caf9
-- title:
--   Appendix B, proof of Theorem 2 — ‖P_T(M)‖ ≤ 2‖M‖
-- statement:
--   Throughout, $A^\star, B^\star \in \mathbb R^{n\times n}$ are real square matrices, $B^\star = U\Sigma V^{T}$ is a compact singular value decomposition with $U, V\in\mathbb R^{n\times k}$ having orthonormal columns and $k = \operatorname{rank}(B^\star)$, $\Omega = \Omega(A^\star)$ is the space of matrices supported inside $\operatorname{support}(A^\star)$, $T = T(B^\star) = \{UX^{T} + YV^{T}\}$, $\mu(A^\star)$ and $\xi(B^\star)$ are the incoherence quantities (1.2) and (1.1), $\|\cdot\|$ is the spectral norm and $\|\cdot\|_\infty$ the largest entry in magnitude.
--
--   For every $M\in\mathbb R^{n\times n}$,
--   $$\|P_{T(B^\star)}(M)\|\le 2\,\|M\|,$$
--   where $P_{T(B^\star)}(M)=P_UM+MP_V-P_UMP_V$ and $\|\cdot\|$ is the spectral norm.
--
--   This bound justifies the first inequality of (B.12).
--
--   **Formalization Note** $P_U$, $P_V$ are built from the given compact SVD datum of $B^\star$.
-- source:
--   Chandrasekaran, Sanghavi, Parrilo, Willsky, Rank-Sparsity Incoherence for Matrix Decomposition, arXiv:0906.2220v1, Appendix B, proof of Theorem 2, p. 19 (justifying (B.12))

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_RankSparsity_Recovery_Setup

open MatrixCompletion

namespace RankSparsity.Recovery

/-- Appendix B, proof of Theorem 2, p. 19 (justifying (B.12)): `‖P_T(M)‖ ≤ 2‖M‖`. -/
theorem tangentProjection_le_two {n r : ℕ} {Bstar : RealMatrix n n} (S : SVD Bstar r)
    (M : RealMatrix n n) :
    spectralNorm (tangentProjection S M) ≤ 2 * spectralNorm M := by sorry

end RankSparsity.Recovery
