-- Prove2me | Theorems.Thm_RankSparsity_Recovery_eq_4_5
-- name    : RankSparsity.Recovery.eq_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:33.796496+00:00
-- url     : https://prove2.me/theorems/a4871063-b847-4e6c-9748-b290754c06de
-- title:
--   (4.5) — characterization of Q ∈ ∂‖B⋆‖_*
-- statement:
--   Throughout, $A^\star, B^\star \in \mathbb R^{n\times n}$ are real square matrices, $B^\star = U\Sigma V^{T}$ is a compact singular value decomposition with $U, V\in\mathbb R^{n\times k}$ having orthonormal columns and $k = \operatorname{rank}(B^\star)$, $\Omega = \Omega(A^\star)$ is the space of matrices supported inside $\operatorname{support}(A^\star)$, $T = T(B^\star) = \{UX^{T} + YV^{T}\}$, $\mu(A^\star)$ and $\xi(B^\star)$ are the incoherence quantities (1.2) and (1.1), $\|\cdot\|$ is the spectral norm and $\|\cdot\|_\infty$ the largest entry in magnitude.
--
--   A matrix $Q$ is a subgradient of the nuclear norm at $B^\star$ if and only if
--   $$P_{T(B^\star)}(Q)=UV^{T},\qquad \|P_{T(B^\star)^\perp}(Q)\|\le 1,$$
--   where $P_{T(B^\star)}(M)=P_UM+MP_V-P_UMP_V$, $P_U=UU^{T}$, $P_V=VV^{T}$, and $P_{T(B^\star)^\perp}=I-P_{T(B^\star)}$.
--
--   This is Watson's description of the subdifferential of the nuclear norm, used for the low-rank half of the dual certificate.
--
--   **Formalization Note** $U$, $V$ and $UV^{T}$ come from the given compact SVD datum of $B^\star$; for $B^\star=0$ the SVD is empty, $UV^{T}=0$, $P_T=0$, and the statement reduces to: $\partial\|0\|_*$ is the unit spectral-norm ball.
-- source:
--   Chandrasekaran, Sanghavi, Parrilo, Willsky, Rank-Sparsity Incoherence for Matrix Decomposition, arXiv:0906.2220v1, §4.1, (4.5), p. 9

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_RankSparsity_Recovery_Setup

open MatrixCompletion

namespace RankSparsity.Recovery

/-- (4.5), p. 9: `Q ∈ ∂‖B⋆‖_*` iff `P_T(Q) = UVᵀ` and `‖P_{T⊥}(Q)‖ ≤ 1`. -/
theorem eq_4_5 {n r : ℕ} (Bstar : RealMatrix n n) (S : SVD Bstar r) (Q : RealMatrix n n) :
    IsSubgrad nuclearNorm Bstar Q ↔
      (tangentProjection S Q = signMatrix S ∧
        spectralNorm (normalProjection S Q) ≤ 1) := by sorry

end RankSparsity.Recovery
