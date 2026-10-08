-- Prove2me | Theorems.Thm_RankSparsity_Recovery_eq_B_13_B_14
-- name    : RankSparsity.Recovery.eq_B_13_B_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:44.031675+00:00
-- url     : https://prove2.me/theorems/b76c67c2-32a2-4cb1-a0ac-040c5e1105cd
-- title:
--   (B.13)–(B.14) — bounds on the errors ε_T and ε_Ω of the dual candidate
-- statement:
--   Throughout, $A^\star, B^\star \in \mathbb R^{n\times n}$ are real square matrices, $B^\star = U\Sigma V^{T}$ is a compact singular value decomposition with $U, V\in\mathbb R^{n\times k}$ having orthonormal columns and $k = \operatorname{rank}(B^\star)$, $\Omega = \Omega(A^\star)$ is the space of matrices supported inside $\operatorname{support}(A^\star)$, $T = T(B^\star) = \{UX^{T} + YV^{T}\}$, $\mu(A^\star)$ and $\xi(B^\star)$ are the incoherence quantities (1.2) and (1.1), $\|\cdot\|$ is the spectral norm and $\|\cdot\|_\infty$ the largest entry in magnitude.
--
--   Assume $\mu(A^\star)\xi(B^\star)<\tfrac16$ and $\gamma\ge0$. Let $Q_\Omega\in\Omega$ and $Q_T\in T$ be such that $\hat Q=Q_\Omega+Q_T$ satisfies $P_\Omega(\hat Q)=\gamma\operatorname{sign}(A^\star)$ and $P_T(\hat Q)=UV^{T}$, and write $Q_\Omega=\gamma\operatorname{sign}(A^\star)+\epsilon_\Omega$, $Q_T=UV^{T}+\epsilon_T$. Then
--   $$\|\epsilon_T\|\le\frac{2\gamma\mu(A^\star)+2\xi(B^\star)\mu(A^\star)}{1-2\xi(B^\star)\mu(A^\star)},\qquad \|\epsilon_\Omega\|_\infty\le\frac{\xi(B^\star)+2\gamma\xi(B^\star)\mu(A^\star)}{1-2\xi(B^\star)\mu(A^\star)}.$$
--
--   These are the quantitative estimates from which the two strict certificate conditions follow.
--
--   **Formalization Note** $\gamma\ge0$ is stated explicitly; on the page it follows from $\gamma>\xi(B^\star)/(1-4\xi(B^\star)\mu(A^\star))\ge0$.
-- source:
--   Chandrasekaran, Sanghavi, Parrilo, Willsky, Rank-Sparsity Incoherence for Matrix Decomposition, arXiv:0906.2220v1, Appendix B, proof of Theorem 2, (B.13)–(B.14), p. 20

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_RankSparsity_Recovery_Setup

open MatrixCompletion

namespace RankSparsity.Recovery

/-- (B.13)–(B.14), p. 20: for `Q̂ = Q_Ω + Q_T` as in the proof of Theorem 2, with
`ε_T = Q_T - UVᵀ` and `ε_Ω = Q_Ω - γ sign(A⋆)`, the two error bounds. -/
theorem eq_B_13_B_14 {n r : ℕ} (γ : ℝ) (Astar Bstar : RealMatrix n n) (S : SVD Bstar r)
    (h : mu Astar * xi S < 1 / 6) (hγ : 0 ≤ γ)
    (QO QT : RealMatrix n n) (hQO : InOmega Astar QO) (hQT : InT S QT)
    (hΩ : projOmega Astar (QO + QT) = γ • entrySign Astar)
    (hT : tangentProjection S (QO + QT) = signMatrix S) :
    spectralNorm (QT - signMatrix S) ≤
        (2 * γ * mu Astar + 2 * xi S * mu Astar) / (1 - 2 * xi S * mu Astar) ∧
      entrySupNorm (QO - γ • entrySign Astar) ≤
        (xi S + 2 * γ * xi S * mu Astar) / (1 - 2 * xi S * mu Astar) := by sorry

end RankSparsity.Recovery
