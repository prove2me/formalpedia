-- Prove2me | Theorems.Thm_RankSparsity_Recovery_dual_candidate
-- name    : RankSparsity.Recovery.dual_candidate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:37.83199+00:00
-- url     : https://prove2.me/theorems/a0342812-ba4c-40d6-b615-3cab6a33c196
-- title:
--   Appendix B, proof of Theorem 2 — the unique dual candidate Q̂ ∈ Ω ⊕ T
-- statement:
--   Throughout, $A^\star, B^\star \in \mathbb R^{n\times n}$ are real square matrices, $B^\star = U\Sigma V^{T}$ is a compact singular value decomposition with $U, V\in\mathbb R^{n\times k}$ having orthonormal columns and $k = \operatorname{rank}(B^\star)$, $\Omega = \Omega(A^\star)$ is the space of matrices supported inside $\operatorname{support}(A^\star)$, $T = T(B^\star) = \{UX^{T} + YV^{T}\}$, $\mu(A^\star)$ and $\xi(B^\star)$ are the incoherence quantities (1.2) and (1.1), $\|\cdot\|$ is the spectral norm and $\|\cdot\|_\infty$ the largest entry in magnitude.
--
--   Assume $\mu(A^\star)\xi(B^\star)<\tfrac16$ and let $\gamma\in\mathbb R$. Then:
--
--   1. there is exactly one matrix $\hat Q\in\Omega\oplus T$ (that is, $\hat Q=Q_\Omega+Q_T$ for some $Q_\Omega\in\Omega$, $Q_T\in T$) such that
--   $$P_\Omega(\hat Q)=\gamma\operatorname{sign}(A^\star),\qquad P_T(\hat Q)=UV^{T};$$
--   2. the splitting of an element of $\Omega+T$ as $Q_\Omega+Q_T$ with $Q_\Omega\in\Omega$, $Q_T\in T$ is unique.
--
--   $\hat Q$ is the candidate dual certificate whose remaining two conditions in Proposition 2 the rest of the proof verifies.
--
--   **Formalization Note** Both existence and uniqueness of $\hat Q$ are asserted, as on the page.
-- source:
--   Chandrasekaran, Sanghavi, Parrilo, Willsky, Rank-Sparsity Incoherence for Matrix Decomposition, arXiv:0906.2220v1, Appendix B, proof of Theorem 2, pp. 18–19

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_RankSparsity_Recovery_Setup

open MatrixCompletion

namespace RankSparsity.Recovery

/-- Appendix B, proof of Theorem 2, p. 18: under `μ(A⋆) ξ(B⋆) < 1/6` there is a unique
`Q̂ ∈ Ω ⊕ T` with `P_Ω(Q̂) = γ sign(A⋆)` and `P_T(Q̂) = UVᵀ`; and the splitting of an
element of `Ω ⊕ T` is unique. -/
theorem dual_candidate {n r : ℕ} (γ : ℝ) (Astar Bstar : RealMatrix n n) (S : SVD Bstar r)
    (h : mu Astar * xi S < 1 / 6) :
    (∃! Q : RealMatrix n n,
      (∃ QO QT : RealMatrix n n, InOmega Astar QO ∧ InT S QT ∧ Q = QO + QT) ∧
        projOmega Astar Q = γ • entrySign Astar ∧
          tangentProjection S Q = signMatrix S) ∧
    (∀ QO QT QO' QT' : RealMatrix n n,
      InOmega Astar QO → InT S QT → InOmega Astar QO' → InT S QT' →
        QO + QT = QO' + QT' → QO = QO' ∧ QT = QT') := by sorry

end RankSparsity.Recovery
