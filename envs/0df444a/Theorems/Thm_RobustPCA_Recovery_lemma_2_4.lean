-- Prove2me | Theorems.Thm_RobustPCA_Recovery_lemma_2_4
-- name    : RobustPCA.Recovery.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:52.89785+00:00
-- url     : https://prove2.me/theorems/58a9817f-e613-43a3-b3b7-c27c8920dcc3
-- title:
--   Lemma 2.4 — an exact dual certificate $(W,F)$ makes $(L_0,S_0)$ the unique solution
-- statement:
--   Throughout, $L_0\in\mathbb R^{n\times n}$ has a compact singular value decomposition $L_0=\sum_{k=1}^r\sigma_k u_kv_k^{*}$ with $\sigma_k>0$ and orthonormal families $(u_k)$, $(v_k)$, so $r=\operatorname{rank}L_0$; $U=[u_1,\dots,u_r]$, $V=[v_1,\dots,v_r]$, and $T=\{UX^*+YV^*\}$ is the tangent space with orthogonal projections $\mathcal P_T$ and $\mathcal P_{T^\perp}=\mathcal I-\mathcal P_T$.
--
--   Let $\lambda>0$, let $S_0\in\mathbb R^{n\times n}$ and $\Omega=\operatorname{supp}(S_0)$. Assume $\|\mathcal P_\Omega\mathcal P_T\|<1$ (operator norm with respect to the Frobenius norm). If there is a pair $(W,F)$ with
--   $$UV^*+W=\lambda\big(\operatorname{sgn}(S_0)+F\big),$$
--   $\mathcal P_TW=0$, $\|W\|<1$, $\mathcal P_\Omega F=0$ and $\|F\|_\infty<1$, then $(L_0,S_0)$ is the unique solution of (1.1) with input $L_0+S_0$.
--
--   This is the optimality certificate for Principal Component Pursuit; Lemma 2.5 relaxes it.
--
--   **Formalization Note** $\lambda>0$ is the paper's standing convention for the weight of (1.1).
-- source:
--   Candès, Li, Ma, Wright, Robust principal component analysis?, J. ACM 58(3) (2011), p. 12, Lemma 2.4

import Definitions.Def_RobustPCA_Recovery_Setup
open MatrixCompletion

namespace RobustPCA.Recovery

/-- Lemma 2.4, p. 12: with `Ω = supp(S0)` and `T` the tangent space of `L0`, if
`‖𝒫_Ω 𝒫_T‖ < 1` and there is `(W, F)` with `UV* + W = λ(sgn(S0) + F)`, `𝒫_T W = 0`, `‖W‖ < 1`,
`𝒫_Ω F = 0` and `‖F‖_∞ < 1`, then `(L0, S0)` is the unique solution of (1.1). -/
theorem lemma_2_4 {n r : ℕ} (lam : ℝ) (L0 S0 : RealMatrix n n) (SV : SVD L0 r)
    (W F : RealMatrix n n) (hlam : 0 < lam)
    (hΩT : ∃ σ < 1, PTOpNormLe (supp S0) SV σ)
    (hcert : signMatrix SV + W = lam • (sgnMatrix S0 + F))
    (hWT : tangentProjection SV W = 0) (hW : spectralNorm W < 1)
    (hFΩ : samplingProjection (supp S0) F = 0) (hF : entrySupNorm F < 1) :
    IsPCPExact lam L0 S0 := by sorry

end RobustPCA.Recovery
