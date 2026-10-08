-- Prove2me | Theorems.Thm_RobustPCA_Recovery_lemma_2_8
-- name    : RobustPCA.Recovery.lemma_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:07.616498+00:00
-- url     : https://prove2.me/theorems/38087c24-f16a-46bd-81bc-0ab713bd1964
-- title:
--   Lemma 2.8 — the golfing certificate $W^L$ obeys $\|W^L\|<1/4$ and the two $\lambda/4$ bounds
-- statement:
--   Throughout, $L_0\in\mathbb R^{n\times n}$ has a compact singular value decomposition $L_0=\sum_{k=1}^r\sigma_k u_kv_k^{*}$ with $\sigma_k>0$ and orthonormal families $(u_k)$, $(v_k)$, so $r=\operatorname{rank}L_0$; $U=[u_1,\dots,u_r]$, $V=[v_1,\dots,v_r]$, and $T=\{UX^*+YV^*\}$ is the tangent space with orthogonal projections $\mathcal P_T$ and $\mathcal P_{T^\perp}=\mathcal I-\mathcal P_T$.
--
--   There are numerical constants $\rho_s>0$, $\rho_r>0$ and $c>0$ with the following property. Let $n\ge1$, let $L_0$ obey (1.2)–(1.3) with parameter $\mu$ and $\operatorname{rank}(L_0)\le\rho_r\,n\,\mu^{-1}(\log n)^{-2}$, let $\lambda=1/\sqrt n$, and let $0<\rho\le\rho_s$. Set $j_0=2\lceil\log n\rceil$ and $q=1-\rho^{1/j_0}$, so that $(1-q)^{j_0}=\rho$. Let $\Omega_1,\dots,\Omega_{j_0}\sim\mathrm{Ber}(q)$ be independent and $\Omega=(\Omega_1\cup\dots\cup\Omega_{j_0})^c$, so that $\Omega\sim\mathrm{Ber}(\rho)$. Define $Y_0=0$, $Y_j=Y_{j-1}+q^{-1}\mathcal P_{\Omega_j}\mathcal P_T(UV^*-Y_{j-1})$ and $W^L=\mathcal P_{T^\perp}Y_{j_0}$ (2.5). Then with probability at least $1-c\,n^{-10}$,
--
--   1. $\|W^L\|<1/4$,
--   2. $\|\mathcal P_\Omega(UV^*+W^L)\|_F<\lambda/4$,
--   3. $\|\mathcal P_{\Omega^\perp}(UV^*+W^L)\|_\infty<\lambda/4$.
--
--   This is the low-rank half of the dual certificate $W=W^L+W^S$.
--
--   **Formalization Note** "The other assumptions of Theorem 1.1" are spelled out: incoherence, the rank condition (written multiplied out, $r\mu(\log n)^2\le\rho_r n$) and $\lambda=1/\sqrt n$. The probability is over the golfing sets $\Omega_1,\dots,\Omega_{j_0}$, which determine $\Omega$. The ceiling is the natural-number ceiling and $\log$ is natural.
-- source:
--   Candès, Li, Ma, Wright, Robust principal component analysis?, J. ACM 58(3) (2011), p. 16, Lemma 2.8 (construction (2.5) p. 14; proof §3.2, pp. 17–19)

import Definitions.Def_RobustPCA_Recovery_Setup
open MatrixCompletion

namespace RobustPCA.Recovery

/-- Lemma 2.8, p. 16: there are numerical constants `ρs, ρr, c > 0` such that, if `L0`
obeys (1.2)–(1.3) and `rank(L0) ≤ ρr n μ⁻¹ (log n)⁻²`, `Ω ∼ Ber(ρ)` with `0 < ρ ≤ ρs`,
`j0 = 2⌈log n⌉`, `Ωᶜ = Ω_1 ∪ ⋯ ∪ Ω_{j0}` with `Ω_j ∼ Ber(q)` i.i.d., `(1 − q)^{j0} = ρ`, and
`λ = 1/√n`, then with probability at least `1 − c n⁻¹⁰` the golfing certificate `W^L` (2.5)
obeys `‖W^L‖ < 1/4`, `‖𝒫_Ω(UV* + W^L)‖_F < λ/4` and `‖𝒫_{Ω⊥}(UV* + W^L)‖_∞ < λ/4`. -/
theorem lemma_2_8 :
    ∃ ρs ρr c : ℝ, 0 < ρs ∧ 0 < ρr ∧ 0 < c ∧
      ∀ (n r : ℕ) (L0 : RealMatrix n n) (SV : SVD L0 r) (μ ρ : ℝ),
        0 < n → Incoherent SV μ → (r : ℝ) * μ * Real.log n ^ 2 ≤ ρr * n →
        0 < ρ → ρ ≤ ρs →
        let j0 := 2 * ⌈Real.log n⌉₊
        let q := 1 - ρ ^ ((1 : ℝ) / j0)
        let lam := 1 / Real.sqrt n
        golfingProb q j0 (fun Ωs =>
            spectralNorm (WL SV q Ωs) < 1 / 4 ∧
            frobeniusNorm (samplingProjection (golfOmega Ωs) (signMatrix SV + WL SV q Ωs)) <
              lam / 4 ∧
            entrySupNorm (compProj (golfOmega Ωs) (signMatrix SV + WL SV q Ωs)) < lam / 4) ≥
          1 - c * (n : ℝ) ^ (-10 : ℤ) := by sorry

end RobustPCA.Recovery
