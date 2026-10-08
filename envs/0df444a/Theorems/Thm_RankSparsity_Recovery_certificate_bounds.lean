-- Prove2me | Theorems.Thm_RankSparsity_Recovery_certificate_bounds
-- name    : RankSparsity.Recovery.certificate_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:35.336913+00:00
-- url     : https://prove2.me/theorems/64fdfcab-bce3-437f-b14c-cdf469311575
-- title:
--   Appendix B, proof of Theorem 2 — ‖P_{T⊥}(Q̂)‖ < 1 and ‖P_{Ωᶜ}(Q̂)‖_∞ < γ
-- statement:
--   Throughout, $A^\star, B^\star \in \mathbb R^{n\times n}$ are real square matrices, $B^\star = U\Sigma V^{T}$ is a compact singular value decomposition with $U, V\in\mathbb R^{n\times k}$ having orthonormal columns and $k = \operatorname{rank}(B^\star)$, $\Omega = \Omega(A^\star)$ is the space of matrices supported inside $\operatorname{support}(A^\star)$, $T = T(B^\star) = \{UX^{T} + YV^{T}\}$, $\mu(A^\star)$ and $\xi(B^\star)$ are the incoherence quantities (1.2) and (1.1), $\|\cdot\|$ is the spectral norm and $\|\cdot\|_\infty$ the largest entry in magnitude.
--
--   Assume $\mu(A^\star)\xi(B^\star)<\tfrac16$ and
--   $$\frac{\xi(B^\star)}{1-4\mu(A^\star)\xi(B^\star)}<\gamma,\qquad \gamma\,\mu(A^\star)<1-3\mu(A^\star)\xi(B^\star).$$
--   Let $Q_\Omega\in\Omega$, $Q_T\in T$ be such that $\hat Q=Q_\Omega+Q_T$ satisfies $P_\Omega(\hat Q)=\gamma\operatorname{sign}(A^\star)$ and $P_T(\hat Q)=UV^{T}$. Then
--   $$\|P_{T^\perp}(\hat Q)\|<1\qquad\text{and}\qquad \|P_{\Omega^c}(\hat Q)\|_\infty<\gamma.$$
--
--   Together with Proposition 1 these are exactly the remaining hypotheses of Proposition 2.
--
--   **Formalization Note** The upper end of the range, $\gamma<(1-3\mu\xi)/\mu$, is written multiplied out as $\gamma\mu<1-3\mu\xi$, which agrees with it when $\mu(A^\star)>0$ and imposes no upper bound when $\mu(A^\star)=0$ (Lean's $x/0=0$ would otherwise empty the range).
-- source:
--   Chandrasekaran, Sanghavi, Parrilo, Willsky, Rank-Sparsity Incoherence for Matrix Decomposition, arXiv:0906.2220v1, Appendix B, proof of Theorem 2, p. 20

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_RankSparsity_Recovery_Setup

open MatrixCompletion

namespace RankSparsity.Recovery

/-- Appendix B, proof of Theorem 2, p. 20: for `γ` in the range of Theorem 2, the
candidate `Q̂ = Q_Ω + Q_T` satisfies `‖P_{T⊥}(Q̂)‖ < 1` and `‖P_{Ωᶜ}(Q̂)‖_∞ < γ`. -/
theorem certificate_bounds {n r : ℕ} (γ : ℝ) (Astar Bstar : RealMatrix n n) (S : SVD Bstar r)
    (h : mu Astar * xi S < 1 / 6)
    (hlow : xi S / (1 - 4 * mu Astar * xi S) < γ)
    (hup : γ * mu Astar < 1 - 3 * mu Astar * xi S)
    (QO QT : RealMatrix n n) (hQO : InOmega Astar QO) (hQT : InT S QT)
    (hΩ : projOmega Astar (QO + QT) = γ • entrySign Astar)
    (hT : tangentProjection S (QO + QT) = signMatrix S) :
    spectralNorm (normalProjection S (QO + QT)) < 1 ∧
      entrySupNorm (projOmegaC Astar (QO + QT)) < γ := by sorry

end RankSparsity.Recovery
