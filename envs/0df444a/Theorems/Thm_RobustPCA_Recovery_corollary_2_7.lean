-- Prove2me | Theorems.Thm_RobustPCA_Recovery_corollary_2_7
-- name    : RobustPCA.Recovery.corollary_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:06.603105+00:00
-- url     : https://prove2.me/theorems/d2f8c610-54b7-4de7-b4b0-9d862cc070ba
-- title:
--   Corollary 2.7 — $\|\mathcal P_\Omega\mathcal P_T\|^2\le\rho+\epsilon$ for $\Omega\sim\mathrm{Ber}(\rho)$
-- statement:
--   Throughout, $L_0\in\mathbb R^{n\times n}$ has a compact singular value decomposition $L_0=\sum_{k=1}^r\sigma_k u_kv_k^{*}$ with $\sigma_k>0$ and orthonormal families $(u_k)$, $(v_k)$, so $r=\operatorname{rank}L_0$; $U=[u_1,\dots,u_r]$, $V=[v_1,\dots,v_r]$, and $T=\{UX^*+YV^*\}$ is the tangent space with orthogonal projections $\mathcal P_T$ and $\mathcal P_{T^\perp}=\mathcal I-\mathcal P_T$.
--
--   There are numerical constants $C_0>0$ and $c>0$ with the following property. Let $n\ge1$, let $L_0$ obey (1.2)–(1.3) with parameter $\mu$, let $0<\epsilon<1$ and $0\le\rho<1$ with
--   $$1-\rho\ge C_0\,\epsilon^{-2}\,\frac{\mu r\log n}{n},$$
--   and let $\Omega\sim\mathrm{Ber}(\rho)$. Then with probability at least $1-c\,n^{-10}$,
--   $$\|\mathcal P_\Omega\mathcal P_T\|^2\le\rho+\epsilon .$$
--
--   For small $\rho$ this makes $\|\mathcal P_\Omega\mathcal P_T\|<1/2$, so that the least-squares certificate $W^S$ is well defined.
--
--   **Formalization Note** The corollary is derived from Theorem 2.6 and holds with high probability, which is stated explicitly. "$C_0$ as in Theorem 2.6" cannot be shared between two statements, so $C_0$ is a fresh existential constant.
-- source:
--   Candès, Li, Ma, Wright, Robust principal component analysis?, J. ACM 58(3) (2011), p. 16, Corollary 2.7 (derivation p. 15)

import Definitions.Def_RobustPCA_Recovery_Setup
open MatrixCompletion

namespace RobustPCA.Recovery

/-- Corollary 2.7, p. 16: there are numerical constants `C0, c > 0` such that, for
`Ω ∼ Ber(ρ)` with `1 − ρ ≥ C0 ε⁻² μr log n / n`, with probability at least `1 − c n⁻¹⁰`,
`‖𝒫_Ω 𝒫_T‖² ≤ ρ + ε`. -/
theorem corollary_2_7 :
    ∃ C0 c : ℝ, 0 < C0 ∧ 0 < c ∧
      ∀ (n r : ℕ) (L0 : RealMatrix n n) (SV : SVD L0 r) (μ ε ρ : ℝ),
        0 < n → Incoherent SV μ → 0 < ε → ε < 1 → 0 ≤ ρ → ρ < 1 →
        1 - ρ ≥ C0 * ε⁻¹ ^ 2 * μ * r * Real.log n / n →
        bernoulliEventProb ρ (fun Ω => PTOpNormLe Ω SV (Real.sqrt (ρ + ε))) ≥
          1 - c * (n : ℝ) ^ (-10 : ℤ) := by sorry

end RobustPCA.Recovery
