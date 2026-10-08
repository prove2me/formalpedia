-- Prove2me | Theorems.Thm_RobustPCA_Recovery_lemma_2_5
-- name    : RobustPCA.Recovery.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:58.358771+00:00
-- url     : https://prove2.me/theorems/2182e052-b39b-46a2-a2f1-a58f66c92458
-- title:
--   Lemma 2.5 — an inexact dual certificate $(W,F,D)$ makes $(L_0,S_0)$ the unique solution
-- statement:
--   Throughout, $L_0\in\mathbb R^{n\times n}$ has a compact singular value decomposition $L_0=\sum_{k=1}^r\sigma_k u_kv_k^{*}$ with $\sigma_k>0$ and orthonormal families $(u_k)$, $(v_k)$, so $r=\operatorname{rank}L_0$; $U=[u_1,\dots,u_r]$, $V=[v_1,\dots,v_r]$, and $T=\{UX^*+YV^*\}$ is the tangent space with orthogonal projections $\mathcal P_T$ and $\mathcal P_{T^\perp}=\mathcal I-\mathcal P_T$.
--
--   Let $0<\lambda<1$, let $S_0\in\mathbb R^{n\times n}$ and $\Omega=\operatorname{supp}(S_0)$, and assume $\|\mathcal P_\Omega\mathcal P_T\|\le1/2$. If there are matrices $W,F,D$ with
--   $$UV^*+W=\lambda\big(\operatorname{sgn}(S_0)+F+\mathcal P_\Omega D\big),$$
--   $\mathcal P_TW=0$, $\|W\|\le\tfrac12$, $\mathcal P_\Omega F=0$, $\|F\|_\infty\le\tfrac12$ and $\|\mathcal P_\Omega D\|_F\le\tfrac14$, then $(L_0,S_0)$ is the unique solution of (1.1) with input $L_0+S_0$.
--
--   The relaxation of the equality constraint $\mathcal P_\Omega(UV^*+W)=\lambda\operatorname{sgn}(S_0)$ is what makes the golfing construction possible.
--
--   **Formalization Note** $\lambda>0$ is the paper's standing convention for the weight of (1.1).
-- source:
--   Candès, Li, Ma, Wright, Robust principal component analysis?, J. ACM 58(3) (2011), p. 13, Lemma 2.5

import Definitions.Def_RobustPCA_Recovery_Setup
open MatrixCompletion

namespace RobustPCA.Recovery

/-- Lemma 2.5, p. 13: with `Ω = supp(S0)`, if `‖𝒫_Ω 𝒫_T‖ ≤ 1/2`, `λ < 1`, and there is
`(W, F, D)` with `UV* + W = λ(sgn(S0) + F + 𝒫_Ω D)`, `𝒫_T W = 0`, `‖W‖ ≤ 1/2`, `𝒫_Ω F = 0`,
`‖F‖_∞ ≤ 1/2` and `‖𝒫_Ω D‖_F ≤ 1/4`, then `(L0, S0)` is the unique solution of (1.1). -/
theorem lemma_2_5 {n r : ℕ} (lam : ℝ) (L0 S0 : RealMatrix n n) (SV : SVD L0 r)
    (W F D : RealMatrix n n) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hΩT : PTOpNormLe (supp S0) SV (1 / 2))
    (hcert : signMatrix SV + W = lam • (sgnMatrix S0 + F + samplingProjection (supp S0) D))
    (hWT : tangentProjection SV W = 0) (hW : spectralNorm W ≤ 1 / 2)
    (hFΩ : samplingProjection (supp S0) F = 0) (hF : entrySupNorm F ≤ 1 / 2)
    (hD : frobeniusNorm (samplingProjection (supp S0) D) ≤ 1 / 4) :
    IsPCPExact lam L0 S0 := by sorry

end RobustPCA.Recovery
