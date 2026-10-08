-- Prove2me | Theorems.Thm_RankSparsity_Recovery_eq_4_3
-- name    : RankSparsity.Recovery.eq_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:33.712985+00:00
-- url     : https://prove2.me/theorems/f7c14fed-61a5-4ddd-9795-1bbcda898eca
-- title:
--   (4.3) — (A⋆, B⋆) optimal for (1.3) iff a common dual Q ∈ γ∂‖A⋆‖₁ ∩ ∂‖B⋆‖_* exists
-- statement:
--   Throughout, $A^\star, B^\star \in \mathbb R^{n\times n}$ are real square matrices, $B^\star = U\Sigma V^{T}$ is a compact singular value decomposition with $U, V\in\mathbb R^{n\times k}$ having orthonormal columns and $k = \operatorname{rank}(B^\star)$, $\Omega = \Omega(A^\star)$ is the space of matrices supported inside $\operatorname{support}(A^\star)$, $T = T(B^\star) = \{UX^{T} + YV^{T}\}$, $\mu(A^\star)$ and $\xi(B^\star)$ are the incoherence quantities (1.2) and (1.1), $\|\cdot\|$ is the spectral norm and $\|\cdot\|_\infty$ the largest entry in magnitude.
--
--   Let $\gamma\ge 0$ and $C=A^\star+B^\star$. Then $(A^\star,B^\star)$ is an optimum of program (1.3),
--   $$\min_{A,B}\ \gamma\|A\|_1+\|B\|_*\quad\text{s.t. } A+B=C,$$
--   if and only if there exists a dual $Q\in\mathbb R^{n\times n}$ with
--   $$Q\in\gamma\,\partial\|A^\star\|_1\quad\text{and}\quad Q\in\partial\|B^\star\|_*.$$
--
--   This is the optimality condition of the convex program (1.3) in subgradient form.
--
--   **Formalization Note** $Q\in\gamma\,\partial\|A^\star\|_1$ is written literally as $Q=\gamma G$ for a subgradient $G$ of $\|\cdot\|_1$ at $A^\star$. "Optimum" means feasible with objective at most that of every feasible pair (not necessarily unique). The hypothesis $\gamma\ge 0$ is the paper's range of the trade-off parameter.
-- source:
--   Chandrasekaran, Sanghavi, Parrilo, Willsky, Rank-Sparsity Incoherence for Matrix Decomposition, arXiv:0906.2220v1, §4.1, (4.3), p. 9

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_RankSparsity_Recovery_Setup

open MatrixCompletion

namespace RankSparsity.Recovery

/-- (4.3), p. 9: for `γ ≥ 0`, `(A⋆, B⋆)` is an optimum of (1.3) with `C = A⋆ + B⋆`
iff some `Q` lies in `γ ∂‖A⋆‖₁` and in `∂‖B⋆‖_*`. -/
theorem eq_4_3 {n : ℕ} (γ : ℝ) (hγ : 0 ≤ γ) (Astar Bstar : RealMatrix n n) :
    IsOptimum γ (Astar + Bstar) Astar Bstar ↔
      ∃ Q : RealMatrix n n,
        (∃ G : RealMatrix n n, IsSubgrad l1Norm Astar G ∧ Q = γ • G) ∧
          IsSubgrad nuclearNorm Bstar Q := by sorry

end RankSparsity.Recovery
