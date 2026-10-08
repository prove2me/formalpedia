-- Prove2me | Theorems.Thm_RobustPCA_Recovery_lemma_2_9
-- name    : RobustPCA.Recovery.lemma_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:57.253587+00:00
-- url     : https://prove2.me/theorems/b8201ff5-9dee-4945-a5d3-d0cc600b8777
-- title:
--   Lemma 2.9 — the least-squares certificate $W^S$ obeys $\|W^S\|<1/4$ and $\|\mathcal P_{\Omega^\perp}W^S\|_\infty<\lambda/4$
-- statement:
--   Throughout, $L_0\in\mathbb R^{n\times n}$ has a compact singular value decomposition $L_0=\sum_{k=1}^r\sigma_k u_kv_k^{*}$ with $\sigma_k>0$ and orthonormal families $(u_k)$, $(v_k)$, so $r=\operatorname{rank}L_0$; $U=[u_1,\dots,u_r]$, $V=[v_1,\dots,v_r]$, and $T=\{UX^*+YV^*\}$ is the tangent space with orthogonal projections $\mathcal P_T$ and $\mathcal P_{T^\perp}=\mathcal I-\mathcal P_T$.
--
--   There are numerical constants $\rho_s>0$, $\rho_r>0$ and $c>0$ with the following property. Let $n\ge1$, let $L_0$ obey (1.2)–(1.3) with parameter $\mu$ and $\operatorname{rank}(L_0)\le\rho_r\,n\,\mu^{-1}(\log n)^{-2}$, let $\lambda=1/\sqrt n$, and let $0<\rho\le\rho_s$. Let $E=\operatorname{sgn}(S_0)$ have independent entries equal to $\pm1$ with probability $\rho/2$ each and $0$ with probability $1-\rho$ (3.7), so that its support $\Omega$ is $\mathrm{Ber}(\rho)$ and its signs are i.i.d. symmetric. Let
--   $$W^S=\lambda\,\mathcal P_{T^\perp}\sum_{k\ge0}(\mathcal P_\Omega\mathcal P_T\mathcal P_\Omega)^kE.\tag{2.7}$$
--   Then with probability at least $1-c\,n^{-10}$: $\|\mathcal P_\Omega\mathcal P_T\|<1/2$ (so that $W^S$ is well defined and equals (2.6)), and
--
--   1. $\|W^S\|<1/4$,
--   2. $\|\mathcal P_{\Omega^\perp}W^S\|_\infty<\lambda/4$.
--
--   This is the sparse half of the dual certificate $W=W^L+W^S$.
--
--   **Formalization Note** Only $\operatorname{sgn}(S_0)$ enters $W^S$, so the random object is $E$. The event includes $\|\mathcal P_\Omega\mathcal P_T\|<1/2$, the standing assumption of the construction of $W^S$. The rank condition is written multiplied out.
-- source:
--   Candès, Li, Ma, Wright, Robust principal component analysis?, J. ACM 58(3) (2011), p. 16, Lemma 2.9 (construction (2.6)–(2.7) p. 15; (3.7) and proof §3.3, pp. 19–21)

import Definitions.Def_RobustPCA_Recovery_Setup
open MatrixCompletion

namespace RobustPCA.Recovery

/-- Lemma 2.9, p. 16: there are numerical constants `ρs, ρr, c > 0` such that, if `L0`
obeys (1.2)–(1.3) and `rank(L0) ≤ ρr n μ⁻¹ (log n)⁻²`, the sign matrix `E = sgn(S0)` follows the
random sign model (3.7) with `0 < ρ ≤ ρs` (support `Ω = supp E ∼ Ber(ρ)`), and `λ = 1/√n`, then
with probability at least `1 − c n⁻¹⁰`, `‖𝒫_Ω 𝒫_T‖ < 1/2` (so `W^S` (2.6) is well defined) and
`‖W^S‖ < 1/4`, `‖𝒫_{Ω⊥} W^S‖_∞ < λ/4`. -/
theorem lemma_2_9 :
    ∃ ρs ρr c : ℝ, 0 < ρs ∧ 0 < ρr ∧ 0 < c ∧
      ∀ (n r : ℕ) (L0 : RealMatrix n n) (SV : SVD L0 r) (μ ρ : ℝ),
        0 < n → Incoherent SV μ → (r : ℝ) * μ * Real.log n ^ 2 ≤ ρr * n →
        0 < ρ → ρ ≤ ρs →
        let lam := 1 / Real.sqrt n
        randomSignProb ρ (fun E : RealMatrix n n =>
            (∃ σ < 1 / 2, PTOpNormLe (supp E) SV σ) ∧
            spectralNorm (WS lam (supp E) SV E) < 1 / 4 ∧
            entrySupNorm (compProj (supp E) (WS lam (supp E) SV E)) < lam / 4) ≥
          1 - c * (n : ℝ) ^ (-10 : ℤ) := by sorry

end RobustPCA.Recovery
