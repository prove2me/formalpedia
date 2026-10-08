-- Prove2me | Theorems.Thm_RobustPCA_Recovery_theorem_2_6
-- name    : RobustPCA.Recovery.theorem_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:53.671072+00:00
-- url     : https://prove2.me/theorems/54b547bb-7163-433f-9f27-9a023c43c7ea
-- title:
--   Theorem 2.6 ([8, Thm 4.1]) — $\|\mathcal P_T-\rho_0^{-1}\mathcal P_T\mathcal P_{\Omega_0}\mathcal P_T\|\le\epsilon$ with high probability
-- statement:
--   Throughout, $L_0\in\mathbb R^{n\times n}$ has a compact singular value decomposition $L_0=\sum_{k=1}^r\sigma_k u_kv_k^{*}$ with $\sigma_k>0$ and orthonormal families $(u_k)$, $(v_k)$, so $r=\operatorname{rank}L_0$; $U=[u_1,\dots,u_r]$, $V=[v_1,\dots,v_r]$, and $T=\{UX^*+YV^*\}$ is the tangent space with orthogonal projections $\mathcal P_T$ and $\mathcal P_{T^\perp}=\mathcal I-\mathcal P_T$.
--
--   There are numerical constants $C_0>0$ and $c>0$ with the following property. Let $n\ge1$, let $L_0$ obey the incoherence condition (1.2)–(1.3) with parameter $\mu$, let $0<\epsilon<1$ and $0<\rho_0\le1$ with
--   $$\rho_0\ge C_0\,\epsilon^{-2}\,\frac{\mu r\log n}{n},$$
--   and let $\Omega_0\sim\mathrm{Ber}(\rho_0)$. Then with probability at least $1-c\,n^{-10}$,
--   $$\|\mathcal P_T-\rho_0^{-1}\mathcal P_T\mathcal P_{\Omega_0}\mathcal P_T\|\le\epsilon,\tag{2.9}$$
--   the operator norm being taken with respect to the Frobenius norm.
--
--   This is the concentration of the sampled tangent-space operator from Candès–Recht; it gives $\|\mathcal P_\Omega\mathcal P_T\|\le1/2$ (Corollary 2.7) and drives the Frobenius contraction of the golfing scheme.
--
--   **Formalization Note** "With high probability" is the paper's $1-O(n^{-10})$, so the constant $c$ is quantified before all data. The bound $\epsilon<1$ is the regime of the cited theorem. $\log$ is the natural logarithm.
-- source:
--   Candès, Li, Ma, Wright, Robust principal component analysis?, J. ACM 58(3) (2011), p. 15, Theorem 2.6 (= Candès–Recht 2009, Theorem 4.1)

import Definitions.Def_RobustPCA_Recovery_Setup
open MatrixCompletion

namespace RobustPCA.Recovery

/-- Theorem 2.6 ([8, Theorem 4.1]), p. 15: there are numerical constants `C0, c > 0` such
that, for `Ω0 ∼ Ber(ρ0)` with `ρ0 ≥ C0 ε⁻² μr log n / n`, with probability at least `1 − c n⁻¹⁰`,
`‖𝒫_T − ρ0⁻¹ 𝒫_T 𝒫_{Ω0} 𝒫_T‖ ≤ ε` (operator norm with respect to `‖·‖_F`). -/
theorem theorem_2_6 :
    ∃ C0 c : ℝ, 0 < C0 ∧ 0 < c ∧
      ∀ (n r : ℕ) (L0 : RealMatrix n n) (SV : SVD L0 r) (μ ε ρ0 : ℝ),
        0 < n → Incoherent SV μ → 0 < ε → ε < 1 → 0 < ρ0 → ρ0 ≤ 1 →
        ρ0 ≥ C0 * ε⁻¹ ^ 2 * μ * r * Real.log n / n →
        bernoulliEventProb ρ0 (fun Ω => ∀ X : RealMatrix n n,
            frobeniusNorm (tangentProjection SV X -
              ρ0⁻¹ • tangentProjection SV (samplingProjection Ω (tangentProjection SV X))) ≤
              ε * frobeniusNorm X) ≥
          1 - c * (n : ℝ) ^ (-10 : ℤ) := by sorry

end RobustPCA.Recovery
