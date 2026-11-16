-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_Supplement_kernel_growth
-- name    : RandomCNFDeficiency.LowerBound.Supplement.kernel_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:03:09.090036+00:00
-- url     : https://prove2.me/theorems/d83396c8-6397-48fa-b497-ec2804dfc0d8
-- title:
--   Lemma A.6 — kernel growth of error sets
-- statement:
--   Fix a prime $p$ and a CNF $F$ on $n$ variables; let $\mathrm{PC}_D$ be the space of polynomials derivable from $Q(F)=\{p_C\}\cup\mathrm{Bool}$ over $\mathbb F_p$ in degree at most $D$, $V_j$ the polynomials of degree at most $j$, and $h(K)=\dim V_K/(\mathrm{PC}_D\cap V_K)$. Let $g_1,\dots,g_s\in V_d$ with $1\le d\le K\le n$ and let $t\ge1$. Set
--
--   $$e=(p-1)d,\qquad \Delta=te,\qquad f_t=\prod_{j=1}^t\bigl(1-q_j^{p-1}\bigr),\qquad q_j=\sum_{i=1}^s\alpha_{j,i}g_i,$$
--
--   where the coefficients $\alpha_{j,i}$ are independent and uniform in $\mathbb F_p$. Let $\mathrm{rk}_{f,K}$ be the rank of $\mathrm{mult}_{f,K}:V_K\to(V_D/\mathrm{PC}_D)^s$, $u\mapsto([fg_iu])_i$, and $\rho_K(d)=1-(1-\tfrac1p)\frac{N_n(K-d)}{N_n(K)}$ with $N_n(j)=\sum_{u\le j}\binom nu$. If $K+\Delta+d\le D$, then
--
--   $$\mathbb E[\mathrm{rk}_{f_t,K}]\le\rho_K(d)^t\,h(K).$$
--
--   Equivalently, the expected dimension of $\ker\mathrm{mult}_{f_t,K}/\mathrm{PC}_D(K)$ is at least $h(K)-\rho_K(d)^t h(K)$.
--
--   This is the kernel-growth estimate behind the common-multiplier argument: multiplying by random Razborov–Smolensky factors shrinks the rank of the error maps geometrically in expectation.
--
--   Differences from the source:
--   - encoding: 𝔽_p[x_1, …, x_n] and G = (g_1, …, g_s) ⊆ V_d → MvPolynomial (Fin n) (ZMod p) and a tuple g : Fin s → polynomials with totalDegree ≤ d; reason: relabelling of the variables; same family
--   - encoding: PC_D, the space of polynomials derivable from Q(F) in degree at most D → the published CD (fpAxioms p F) D: tree-shaped derivations of degree ≤ D from Bool ∪ {p_C}, with 0 included; reason: the source treats PC_D as a vector space; tree and sequence derivations have the same consequences
--   - encoding: mult_{f,K} : V_K → (V_D/PC_D)^s → the published errorMap into (𝔽_p[x]/PC_D)^s and its rank cRank; reason: PC_D ⊆ V_D, so V_D/PC_D embeds in the quotient of the whole ring and the rank is unchanged when f g_i u ∈ V_D
--   - encoding: expectation over independent uniform α_{j,i} → the exact average over all coefficient arrays in 𝔽_p^{t×s}; reason: the uniform product measure on a finite set
--   - encoding: dim ker mult_{f_t,K}/PC_D(K) → the dimension of ker mult_{f_t,K} modulo its intersection with PC_D ∩ V_K; reason: under the degree budget PC_D(K) ⊆ ker mult_{f_t,K} (73), so the two quotients coincide
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Lemma A.6, Equation (75), printed p. 26, PDF p. 28; Equations (47), (48), (72), printed pp. 20–21, 25, PDF pp. 22–23, 27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_RSApproximation
set_option autoImplicit false

namespace RandomCNFDeficiency.LowerBound.Supplement

open RandomCNFDeficiency.LowerBound
open ResPCDegreeSize.Main (Poly hDim eta)

/-- Conneryd, STOC 2027 #332, Lemma A.6 (kernel growth), Equation (75): for `g_1, …, g_s` of
degree at most `d`, `1 ≤ d ≤ K ≤ n`, `t ≥ 1`, `Δ = t (p - 1) d` and `K + Δ + d ≤ D`, the
expected rank of `mult_{f_t,K}` over independent uniform coefficients is at most
`ρ_K(d)^t h(K)`, where `ρ_K(d) = 1 - η_K(d)`; equivalently the expected dimension of
`ker mult_{f_t,K} / PC_D(K)` is at least `h(K) - ρ_K(d)^t h(K)`. -/
theorem kernel_growth {p n s d K D t : ℕ} [Fact p.Prime] (F : CNF n)
    (g : Fin s → Poly n p) (hg : ∀ i, (g i).totalDegree ≤ d)
    (hd : 1 ≤ d) (hdK : d ≤ K) (hKn : K ≤ n) (ht : 1 ≤ t)
    (hD : K + t * ((p - 1) * d) + d ≤ D) :
    expectedRank (fpAxioms p F) D g t K ≤
        (1 - eta p n K d) ^ t * (hDim (fpAxioms p F) D K : ℝ) ∧
    (hDim (fpAxioms p F) D K : ℝ) - (1 - eta p n K d) ^ t * (hDim (fpAxioms p F) D K : ℝ) ≤
        expectedKernelQuotientDim (fpAxioms p F) D g t K := by sorry

end RandomCNFDeficiency.LowerBound.Supplement
