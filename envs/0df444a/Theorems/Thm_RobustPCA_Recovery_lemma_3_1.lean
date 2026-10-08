-- Prove2me | Theorems.Thm_RobustPCA_Recovery_lemma_3_1
-- name    : RobustPCA.Recovery.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:54.883979+00:00
-- url     : https://prove2.me/theorems/34329952-e08b-43e5-a127-8c2329f393f3
-- title:
--   Lemma 3.1 — $\|Z-\rho_0^{-1}\mathcal P_T\mathcal P_{\Omega_0}Z\|_\infty\le\epsilon\|Z\|_\infty$ for fixed $Z\in T$
-- statement:
--   Throughout, $L_0\in\mathbb R^{n\times n}$ has a compact singular value decomposition $L_0=\sum_{k=1}^r\sigma_k u_kv_k^{*}$ with $\sigma_k>0$ and orthonormal families $(u_k)$, $(v_k)$, so $r=\operatorname{rank}L_0$; $U=[u_1,\dots,u_r]$, $V=[v_1,\dots,v_r]$, and $T=\{UX^*+YV^*\}$ is the tangent space with orthogonal projections $\mathcal P_T$ and $\mathcal P_{T^\perp}=\mathcal I-\mathcal P_T$.
--
--   There are numerical constants $C_0>0$ and $c>0$ with the following property. Let $n\ge1$, let $L_0$ obey (1.2)–(1.3) with parameter $\mu$, let $Z\in T$ be a fixed matrix, let $0<\epsilon\le1$ and $0<\rho_0\le1$ with
--   $$\rho_0\ge C_0\,\epsilon^{-2}\,\frac{\mu r\log n}{n},$$
--   and let $\Omega_0\sim\mathrm{Ber}(\rho_0)$. Then with probability at least $1-c\,n^{-10}$,
--   $$\|Z-\rho_0^{-1}\mathcal P_T\mathcal P_{\Omega_0}Z\|_\infty\le\epsilon\,\|Z\|_\infty.\tag{3.1}$$
--
--   This sup-norm contraction drives the entrywise estimates of the golfing scheme in Lemma 2.8.
--
--   **Formalization Note** The matrix $Z$ is quantified before the probability, as the lemma requires it to be fixed. The restriction $\epsilon\le1$ is the regime of the Bernstein argument in §7.2 (the paper uses $\epsilon\le e^{-1}$).
-- source:
--   Candès, Li, Ma, Wright, Robust principal component analysis?, J. ACM 58(3) (2011), p. 16, Lemma 3.1 (proof §7.2, pp. 31–32)

import Definitions.Def_RobustPCA_Recovery_Setup
open MatrixCompletion

namespace RobustPCA.Recovery

/-- Lemma 3.1, p. 16: there are numerical constants `C0, c > 0` such that, for a fixed
`Z ∈ T` and `Ω0 ∼ Ber(ρ0)` with `ρ0 ≥ C0 ε⁻² μr log n / n`, with probability at least
`1 − c n⁻¹⁰`, `‖Z − ρ0⁻¹ 𝒫_T 𝒫_{Ω0} Z‖_∞ ≤ ε ‖Z‖_∞`. -/
theorem lemma_3_1 :
    ∃ C0 c : ℝ, 0 < C0 ∧ 0 < c ∧
      ∀ (n r : ℕ) (L0 : RealMatrix n n) (SV : SVD L0 r) (μ : ℝ) (Z : RealMatrix n n)
        (ε ρ0 : ℝ),
        0 < n → Incoherent SV μ → tangentProjection SV Z = Z → 0 < ε → ε ≤ 1 →
        0 < ρ0 → ρ0 ≤ 1 → ρ0 ≥ C0 * ε⁻¹ ^ 2 * μ * r * Real.log n / n →
        bernoulliEventProb ρ0 (fun Ω =>
            entrySupNorm (Z - ρ0⁻¹ • tangentProjection SV (samplingProjection Ω Z)) ≤
              ε * entrySupNorm Z) ≥
          1 - c * (n : ℝ) ^ (-10 : ℤ) := by sorry

end RobustPCA.Recovery
