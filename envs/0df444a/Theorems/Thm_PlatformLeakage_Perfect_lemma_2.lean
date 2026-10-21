-- Prove2me | Theorems.Thm_PlatformLeakage_Perfect_lemma_2
-- name    : PlatformLeakage.Perfect.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:34.156104+00:00
-- url     : https://prove2.me/theorems/a92cb217-6f80-46c1-99ae-25a71f248890
-- title:
--   Lemma 2, p. 16 — optimal fees Q^j_p(n) = g1(n, v^j), Q^j_o = g1(1, v^j − Ro) and utility rates U^j_p = ωg2(n, v^j) − K^j, U^j_o = g2(1, v^j − Ro) − K^j
-- statement:
--   Under the standing assumptions, fix a provider type $j$ and recall $g_1,g_2$ of (18).
--
--   1. For every $n\ge1$, the on-platform revenue rate $\zeta\mapsto\zeta\lambda^j_p(n,\zeta)$ over fees $\zeta\ge0$ has maximum value $g_2(n,v^j)$, and a fee $\zeta\ge0$ attains it if and only if $\zeta=g_1(n,v^j)$. Consequently the symmetric on-platform fee and utility rate are
--   $$Q^j_p(n)=g_1(n,v^j),\qquad U^j_p(\omega,n)=\omega\,g_2(n,v^j)-K^j\quad\text{for all }\omega,$$
--   and the symmetric-equilibrium condition (8) holds: $\max_{q\ge0}q\lambda^j_p(1,q)\le Q^j_p(n)\lambda^j_p(n,Q^j_p(n))$.
--   2. The off-platform revenue rate $q\mapsto q\lambda^j_o(q)$ over $q\ge0$ has maximum value $g_2(1,(v^j-R_o)^+)$, so
--   $$U^j_o=g_2\big(1,(v^j-R_o)^+\big)-K^j.$$
--   3. If $R_o<v^j$, a fee $q\ge0$ attains this maximum if and only if $q=Q^j_o=g_1(1,v^j-R_o)$.
--
--   These closed forms reduce the providers' participation game to a comparison of $\omega g_2(n,v^j)$ with $\widehat K^j$, which is the content of Proposition 1.
--
--   **Formalization Note** The paper writes $g_2(1,v^j-R_o)$; the positive part keeps $g_2$ on its domain $\mathbb R^2_+$ and agrees with it when $R_o<v^j$. When $R_o\ge v^j$ the off-platform demand is zero at every fee, so every fee is optimal; uniqueness of the off-platform fee is therefore stated only for $R_o<v^j$.
-- source:
--   He, Savin, Goh & Teo, Off-Platform Threats in On-Demand Services, SSRN working paper 3550646 (PDF of 2021-03-25), p. 16 (PDF 16), Lemma 2, (8), (19)–(20); proof, Appendix pp. 1–2 (PDF 36–37)

import Mathlib
import Definitions.Def_PlatformLeakage_Perfect_Model

namespace PlatformLeakage.Perfect

/-- Lemma 2 (p. 16): for `n ≥ 1` providers sharing a fee, the on-platform revenue `ζ λ^j_p(n, ζ)` over
`ζ ≥ 0` has maximum `g2(n, v^j)`, attained exactly at `ζ = g1(n, v^j)`; hence `Q^j_p(n) = g1(n, v^j)`,
`U^j_p(ω, n) = ω g2(n, v^j) − K^j`, and the symmetric-equilibrium condition (8) holds. The off-platform
revenue `q λ^j_o(q)` over `q ≥ 0` has maximum `g2(1, (v^j − R_o)⁺)`, so `U^j_o = g2(1, (v^j − R_o)⁺) − K^j`,
and when `R_o < v^j` the maximum is attained exactly at `q = g1(1, v^j − R_o)`. -/
theorem lemma_2 (P : Params) (hP : P.Std) (j : PType) :
    (∀ n : ℕ, 1 ≤ n →
      IsGreatest ((fun ζ : ℝ => ζ * demandP P j n ζ) '' Set.Ici 0) (g2 P n (P.v j)) ∧
      (∀ ζ : ℝ, 0 ≤ ζ → (ζ * demandP P j n ζ = g2 P n (P.v j) ↔ ζ = g1 P n (P.v j))) ∧
      feeP P j n = g1 P n (P.v j) ∧
      (∀ ω : ℝ, Up P j ω n = ω * g2 P n (P.v j) - P.K j) ∧
      onValue P j 1 ≤ feeP P j n * demandP P j n (feeP P j n)) ∧
    IsGreatest ((fun q : ℝ => q * demandO P j q) '' Set.Ici 0) (g2 P 1 (max (P.v j - P.Ro) 0)) ∧
    Uo P j = g2 P 1 (max (P.v j - P.Ro) 0) - P.K j ∧
    (P.Ro < P.v j → ∀ q : ℝ, 0 ≤ q →
      (q * demandO P j q = g2 P 1 (P.v j - P.Ro) ↔ q = g1 P 1 (P.v j - P.Ro))) := by sorry

end PlatformLeakage.Perfect
