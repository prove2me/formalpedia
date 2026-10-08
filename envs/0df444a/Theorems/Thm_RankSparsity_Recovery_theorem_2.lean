-- Prove2me | Theorems.Thm_RankSparsity_Recovery_theorem_2
-- name    : RankSparsity.Recovery.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:38.17847+00:00
-- url     : https://prove2.me/theorems/436ac55c-9b62-4ae6-bb33-45756c07a127
-- title:
--   Theorem 2 — μ(A⋆)ξ(B⋆) < 1/6 gives exact recovery for γ in an explicit interval
-- statement:
--   Throughout, $A^\star, B^\star \in \mathbb R^{n\times n}$ are real square matrices, $B^\star = U\Sigma V^{T}$ is a compact singular value decomposition with $U, V\in\mathbb R^{n\times k}$ having orthonormal columns and $k = \operatorname{rank}(B^\star)$, $\Omega = \Omega(A^\star)$ is the space of matrices supported inside $\operatorname{support}(A^\star)$, $T = T(B^\star) = \{UX^{T} + YV^{T}\}$, $\mu(A^\star)$ and $\xi(B^\star)$ are the incoherence quantities (1.2) and (1.1), $\|\cdot\|$ is the spectral norm and $\|\cdot\|_\infty$ the largest entry in magnitude.
--
--   **Theorem 2.** Let $C=A^\star+B^\star$ with
--   $$\mu(A^\star)\,\xi(B^\star)<\frac16 .$$
--   Then for every $\gamma$ with
--   $$\gamma\in\left(\frac{\xi(B^\star)}{1-4\mu(A^\star)\xi(B^\star)},\ \frac{1-3\mu(A^\star)\xi(B^\star)}{\mu(A^\star)}\right)$$
--   the unique optimum $(\hat A,\hat B)$ of
--   $$\min_{A,B}\ \gamma\|A\|_1+\|B\|_*\quad\text{s.t. } A+B=C \tag{1.3}$$
--   is $(A^\star,B^\star)$. Moreover, when $A^\star\neq0$ and $B^\star\neq0$, the value $\gamma=\sqrt{3\xi(B^\star)/(2\mu(A^\star))}$ lies strictly inside this interval.
--
--   This is the main theorem of the paper: a deterministic condition, depending only on the support of $A^\star$ and the row and column spaces of $B^\star$, under which the convex program (1.3) recovers the sparse and low-rank components exactly.
--
--   **Formalization Note** "Unique optimum" is strict: every other feasible pair has strictly larger objective. The upper end of the interval is written multiplied out, $\gamma\,\mu(A^\star)<1-3\mu(A^\star)\xi(B^\star)$; this is the same condition when $\mu(A^\star)>0$ and means "no upper bound" when $A^\star=0$, where Lean's convention $x/0=0$ would otherwise empty the interval. The "specifically" clause divides by $\mu(A^\star)$ and needs $\xi(B^\star)>0$, so it is stated under $A^\star\neq0$, $B^\star\neq0$, which the paper leaves implicit. $T(B^\star)$, $UV^{T}$ and $\xi(B^\star)$ are taken with respect to a given compact SVD of $B^\star$; the theorem holds for every such SVD.
-- source:
--   Chandrasekaran, Sanghavi, Parrilo, Willsky, Rank-Sparsity Incoherence for Matrix Decomposition, arXiv:0906.2220v1, Theorem 2, p. 10

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_RankSparsity_Recovery_Setup

open MatrixCompletion

namespace RankSparsity.Recovery

/-- Theorem 2 (p. 10): if `μ(A⋆) ξ(B⋆) < 1/6`, then for every
`γ ∈ (ξ(B⋆)/(1 - 4μ(A⋆)ξ(B⋆)), (1 - 3μ(A⋆)ξ(B⋆))/μ(A⋆))` the unique optimum of (1.3)
with `C = A⋆ + B⋆` is `(A⋆, B⋆)`; and (for `A⋆, B⋆ ≠ 0`) `γ = √(3ξ(B⋆)/(2μ(A⋆)))` lies in
that range. The upper end is written multiplied out, `γ μ(A⋆) < 1 - 3μ(A⋆)ξ(B⋆)`. -/
theorem theorem_2 {n r : ℕ} (Astar Bstar : RealMatrix n n) (S : SVD Bstar r)
    (h : mu Astar * xi S < 1 / 6) :
    (∀ γ : ℝ, xi S / (1 - 4 * mu Astar * xi S) < γ →
        γ * mu Astar < 1 - 3 * mu Astar * xi S →
        IsUniqueOptimum γ (Astar + Bstar) Astar Bstar) ∧
    (Astar ≠ 0 → Bstar ≠ 0 →
        xi S / (1 - 4 * mu Astar * xi S) < Real.sqrt (3 * xi S / (2 * mu Astar)) ∧
        Real.sqrt (3 * xi S / (2 * mu Astar)) < (1 - 3 * mu Astar * xi S) / mu Astar) := by sorry

end RankSparsity.Recovery
