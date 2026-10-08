-- Prove2me | Theorems.Thm_RobustPCA_Recovery_eq_2_2
-- name    : RobustPCA.Recovery.eq_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:52.447837+00:00
-- url     : https://prove2.me/theorems/345bacb9-6a9f-4cc0-bdec-1bcdb94d47a9
-- title:
--   (2.2) — $\|\mathcal P_T e_ie_j^*\|_F\le\sqrt{2\mu r/n}$ under incoherence
-- statement:
--   Throughout, $L_0\in\mathbb R^{n\times n}$ has a compact singular value decomposition $L_0=\sum_{k=1}^r\sigma_k u_kv_k^{*}$ with $\sigma_k>0$ and orthonormal families $(u_k)$, $(v_k)$, so $r=\operatorname{rank}L_0$; $U=[u_1,\dots,u_r]$, $V=[v_1,\dots,v_r]$, and $T=\{UX^*+YV^*\}$ is the tangent space with orthogonal projections $\mathcal P_T$ and $\mathcal P_{T^\perp}=\mathcal I-\mathcal P_T$.
--
--   Suppose $L_0$ obeys the incoherence condition (1.2)–(1.3) with parameter $\mu$, and $\mu r/n\le1$. Then for every coordinate matrix $e_ie_j^*$,
--   $$\|\mathcal P_T\,e_ie_j^*\|_F\le\sqrt{\frac{2\mu r}{n}}.\tag{2.2}$$
--
--   This pointwise bound controls the size of each coordinate matrix in the tangent space; it is the source of the variance bounds in the proofs of Lemma 3.1 and Lemma 2.9.
-- source:
--   Candès, Li, Ma, Wright, Robust principal component analysis?, J. ACM 58(3) (2011), p. 10, (2.2)

import Definitions.Def_RobustPCA_Recovery_Setup
open MatrixCompletion

namespace RobustPCA.Recovery

/-- (2.2), p. 10: under the incoherence condition (only (1.2) is used) and `μr/n ≤ 1`,
`‖𝒫_T e_i e_j*‖_F ≤ √(2μr/n)` for every coordinate matrix `e_i e_j*`. -/
theorem eq_2_2 {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (μ : ℝ)
    (hinc : Incoherent SV μ) (hμr : μ * r ≤ n) (i j : Fin n) :
    frobeniusNorm (tangentProjection SV (coordinateMatrix i j)) ≤
      Real.sqrt (2 * μ * r / n) := by sorry

end RobustPCA.Recovery
