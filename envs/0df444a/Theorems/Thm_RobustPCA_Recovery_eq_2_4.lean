-- Prove2me | Theorems.Thm_RobustPCA_Recovery_eq_2_4
-- name    : RobustPCA.Recovery.eq_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:54.952223+00:00
-- url     : https://prove2.me/theorems/0363db4b-316e-4cfb-9239-bca12d162ae2
-- title:
--   (2.4) — a dual certificate $W$ obeying (2.4) certifies exact recovery
-- statement:
--   Throughout, $L_0\in\mathbb R^{n\times n}$ has a compact singular value decomposition $L_0=\sum_{k=1}^r\sigma_k u_kv_k^{*}$ with $\sigma_k>0$ and orthonormal families $(u_k)$, $(v_k)$, so $r=\operatorname{rank}L_0$; $U=[u_1,\dots,u_r]$, $V=[v_1,\dots,v_r]$, and $T=\{UX^*+YV^*\}$ is the tangent space with orthogonal projections $\mathcal P_T$ and $\mathcal P_{T^\perp}=\mathcal I-\mathcal P_T$.
--
--   Let $0<\lambda<1$, $S_0\in\mathbb R^{n\times n}$, $\Omega=\operatorname{supp}(S_0)$, and assume $\|\mathcal P_\Omega\mathcal P_T\|\le1/2$. If a matrix $W$ obeys
--   $$W\in T^\perp,\qquad \|W\|<\tfrac12,\qquad \|\mathcal P_\Omega(UV^*-\lambda\operatorname{sgn}(S_0)+W)\|_F\le\tfrac\lambda4,\qquad \|\mathcal P_{\Omega^\perp}(UV^*+W)\|_\infty<\tfrac\lambda2,\tag{2.4}$$
--   then $(L_0,S_0)$ is the unique solution of (1.1) with input $L_0+S_0$.
--
--   This is the form of the certificate that the proof of Theorem 1.1 constructs, as $W=W^L+W^S$.
-- source:
--   Candès, Li, Ma, Wright, Robust principal component analysis?, J. ACM 58(3) (2011), p. 14, §2.3, (2.4)

import Definitions.Def_RobustPCA_Recovery_Setup
open MatrixCompletion

namespace RobustPCA.Recovery

/-- (2.4), p. 14: under the assumptions of Lemma 2.5 on `Ω = supp(S0)`, `T` and `λ`, a dual
certificate `W ∈ T⊥` with `‖W‖ < 1/2`, `‖𝒫_Ω(UV* − λ sgn(S0) + W)‖_F ≤ λ/4` and
`‖𝒫_{Ω⊥}(UV* + W)‖_∞ < λ/2` certifies that `(L0, S0)` is the unique solution of (1.1). -/
theorem eq_2_4 {n r : ℕ} (lam : ℝ) (L0 S0 : RealMatrix n n) (SV : SVD L0 r)
    (W : RealMatrix n n) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hΩT : PTOpNormLe (supp S0) SV (1 / 2))
    (hWT : tangentProjection SV W = 0) (hW : spectralNorm W < 1 / 2)
    (hΩ : frobeniusNorm (samplingProjection (supp S0) (signMatrix SV - lam • sgnMatrix S0 + W))
      ≤ lam / 4)
    (hΩc : entrySupNorm (compProj (supp S0) (signMatrix SV + W)) < lam / 2) :
    IsPCPExact lam L0 S0 := by sorry

end RobustPCA.Recovery
