-- Prove2me | Theorems.Thm_RankSparsity_Recovery_eq_4_4
-- name    : RankSparsity.Recovery.eq_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:31.282229+00:00
-- url     : https://prove2.me/theorems/6f21a1c1-169d-4ece-a3b4-4651556f1a80
-- title:
--   (4.4) — characterization of Q ∈ γ∂‖A⋆‖₁
-- statement:
--   Throughout, $A^\star, B^\star \in \mathbb R^{n\times n}$ are real square matrices, $B^\star = U\Sigma V^{T}$ is a compact singular value decomposition with $U, V\in\mathbb R^{n\times k}$ having orthonormal columns and $k = \operatorname{rank}(B^\star)$, $\Omega = \Omega(A^\star)$ is the space of matrices supported inside $\operatorname{support}(A^\star)$, $T = T(B^\star) = \{UX^{T} + YV^{T}\}$, $\mu(A^\star)$ and $\xi(B^\star)$ are the incoherence quantities (1.2) and (1.1), $\|\cdot\|$ is the spectral norm and $\|\cdot\|_\infty$ the largest entry in magnitude.
--
--   Let $\gamma\ge 0$. A matrix $Q$ belongs to $\gamma\,\partial\|A^\star\|_1$ if and only if
--   $$P_{\Omega(A^\star)}(Q)=\gamma\operatorname{sign}(A^\star),\qquad \|P_{\Omega(A^\star)^c}(Q)\|_\infty\le\gamma,$$
--   where $\operatorname{sign}(A^\star_{ij})$ is $+1$, $-1$ or $0$ according as $A^\star_{ij}>0$, $<0$ or $=0$.
--
--   This is the entrywise description of the scaled $\ell_1$ subdifferential used for the sparse half of the dual certificate.
--
--   **Formalization Note** $Q\in\gamma\,\partial\|A^\star\|_1$ is written as $Q=\gamma G$ with $G$ a subgradient of $\|\cdot\|_1$ at $A^\star$. The case $\gamma=0$ is included (both sides then say $Q=0$).
-- source:
--   Chandrasekaran, Sanghavi, Parrilo, Willsky, Rank-Sparsity Incoherence for Matrix Decomposition, arXiv:0906.2220v1, §4.1, (4.4), p. 9

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_RankSparsity_Recovery_Setup

open MatrixCompletion

namespace RankSparsity.Recovery

/-- (4.4), p. 9: for `γ ≥ 0`, `Q ∈ γ ∂‖A⋆‖₁` iff `P_Ω(Q) = γ sign(A⋆)` and
`‖P_{Ωᶜ}(Q)‖_∞ ≤ γ`. -/
theorem eq_4_4 {n : ℕ} (γ : ℝ) (hγ : 0 ≤ γ) (Astar Q : RealMatrix n n) :
    (∃ G : RealMatrix n n, IsSubgrad l1Norm Astar G ∧ Q = γ • G) ↔
      (projOmega Astar Q = γ • entrySign Astar ∧
        entrySupNorm (projOmegaC Astar Q) ≤ γ) := by sorry

end RankSparsity.Recovery
