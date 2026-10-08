-- Prove2me | Theorems.Thm_RankSparsity_Recovery_eq_B_6
-- name    : RankSparsity.Recovery.eq_B_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:43.43898+00:00
-- url     : https://prove2.me/theorems/b38b8be2-23a1-445c-b364-97d216ad81d3
-- title:
--   (B.6) — μξ < 1/6 makes the γ-range of Theorem 2 nonempty
-- statement:
--   Throughout, $A^\star, B^\star \in \mathbb R^{n\times n}$ are real square matrices, $B^\star = U\Sigma V^{T}$ is a compact singular value decomposition with $U, V\in\mathbb R^{n\times k}$ having orthonormal columns and $k = \operatorname{rank}(B^\star)$, $\Omega = \Omega(A^\star)$ is the space of matrices supported inside $\operatorname{support}(A^\star)$, $T = T(B^\star) = \{UX^{T} + YV^{T}\}$, $\mu(A^\star)$ and $\xi(B^\star)$ are the incoherence quantities (1.2) and (1.1), $\|\cdot\|$ is the spectral norm and $\|\cdot\|_\infty$ the largest entry in magnitude.
--
--   If $\xi(B^\star)\,\mu(A^\star)<\tfrac16$ and $\mu(A^\star)>0$, then
--   $$\frac{\xi(B^\star)}{1-4\xi(B^\star)\mu(A^\star)}<\frac{1-3\xi(B^\star)\mu(A^\star)}{\mu(A^\star)}.$$
--
--   So the interval of trade-off parameters $\gamma$ in Theorem 2 is nonempty.
--
--   **Formalization Note** The hypothesis $\mu(A^\star)>0$ is added because the right-hand side divides by $\mu(A^\star)$; in Lean $x/0=0$. It holds whenever $A^\star\neq0$.
-- source:
--   Chandrasekaran, Sanghavi, Parrilo, Willsky, Rank-Sparsity Incoherence for Matrix Decomposition, arXiv:0906.2220v1, Appendix B, proof of Theorem 2, (B.6), p. 18

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_RankSparsity_Recovery_Setup

open MatrixCompletion

namespace RankSparsity.Recovery

/-- (B.6), p. 18: if `ξ(B⋆) μ(A⋆) < 1/6` (and `μ(A⋆) > 0`) the range of `γ` in
Theorem 2 is nonempty. -/
theorem eq_B_6 {n r : ℕ} (Astar Bstar : RealMatrix n n) (S : SVD Bstar r)
    (h : xi S * mu Astar < 1 / 6) (hmu : 0 < mu Astar) :
    xi S / (1 - 4 * xi S * mu Astar) < (1 - 3 * xi S * mu Astar) / mu Astar := by sorry

end RankSparsity.Recovery
