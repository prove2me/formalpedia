-- Prove2me | Theorems.Thm_PDSEquiv_lemma_7_3
-- name    : PDSEquiv.lemma_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:02:33.820332+00:00
-- url     : https://prove2.me/theorems/cc2d8cf1-bedf-4406-92c4-75857a268620
-- title:
--   Lemma 7.3 — the conditional means $\mu_0,\mu_1$ of the vertex scores, $\mu_0-\mu_1$, and (10)
-- statement:
--   Fix rationals $0<q<p\le1$, $\gamma\in(0,1]$, integers $1\le\kappa\le n\le N-1$ and real $K\in[1,N-1]$ (the standing assumptions of §7.1). Let $O$ be a distinguisher on $n$-vertex graphs with acceptance probabilities in $[0,1]$, let $x=(1-q)nK/N$ and $\theta,L,h,Z_v$ as in §7.2. For every $v\in[N]$, over $(G,C)\sim\widetilde{\mathrm{PDS}}(N,K,p,q)$,
--   $$\mu_0:=\mathbb E[Z_v(G)\mid v\notin C]=\frac1L\sum_{\ell=0}^{L-1}h(x\theta^\ell),\qquad \mu_1:=\mathbb E[Z_v(G)\mid v\in C]=\frac1L\sum_{\ell=0}^{L-1}h(x\theta^{\ell+1}),$$
--   $$\mu_0-\mu_1=\frac{h(x)-h(x\theta^L)}L.$$
--   If $O$ satisfies (8), $x\ge4$, $\kappa\le(1-q)nK/(4N)$ and $N\ge8/\gamma$, then
--   $$\mu_0-\mu_1\ge\frac\gamma{4L}.\tag{10}$$
--
--   Planted vertices have a strictly smaller expected score, which is what thresholding exploits.
--
--   Differences from the source:
--   - encoding: standing assumptions of §7.1 (γ ∈ (0, 1], 1 ≤ κ ≤ n ≤ N − 1, K ∈ [1, N − 1]) and of §7 (rationals 0 < q < p ≤ 1) → binders; reason: the section's standing assumptions
--   - encoding: a randomized distinguisher O on n-vertex graphs → its acceptance function a : G_n → [0, 1]; reason: every quantity in the lemma depends on O only through a
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), Lemma 7.3, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_PDSEquiv_Laws
import Definitions.Def_PDSEquiv_Thin

set_option autoImplicit false

namespace PDSEquiv

/-- S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), Lemma 7.3, p.28 (PDF p.30).
The conditional means of the vertex scores, their difference, and (10).

**Formalization Note.** The standing assumptions of §7.1 are binders: rationals `0 < q < p ≤ 1`,
`γ ∈ (0, 1]`, integers `1 ≤ κ ≤ n ≤ N − 1`, real `K ∈ [1, N − 1]`. `a` is the acceptance function of
`O`; the formulas hold for any `a` with values in `[0, 1]`, and (10) under (8). -/
theorem lemma_7_3 (p q : ℚ) (hq : 0 < q) (hqp : q < p) (hp : p ≤ 1) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (N n κ : ℕ) (hκ : 1 ≤ κ) (hκn : κ ≤ n) (hnN : n + 1 ≤ N) (K : ℝ) (hK : 1 ≤ K)
    (hKN : K ≤ (N : ℝ) - 1) (a : Graph n → ℝ) (ha : ∀ H, 0 ≤ a H ∧ a H ≤ 1) (v : Fin N) :
    let θ : ℝ := theta p q
    let L : ℕ := levelL p q N
    let x : ℝ := (1 - (q : ℝ)) * n * K / N
    let μ₀ : ℝ := condMean K p q a v false
    let μ₁ : ℝ := condMean K p q a v true
    μ₀ = (L : ℝ)⁻¹ * ∑ ℓ ∈ Finset.range L, hFun p q a (x * θ ^ ℓ) ∧
    μ₁ = (L : ℝ)⁻¹ * ∑ ℓ ∈ Finset.range L, hFun p q a (x * θ ^ (ℓ + 1)) ∧
    μ₀ - μ₁ = (hFun p q a x - hFun p q a (x * θ ^ L)) / L ∧
    (IsAdversarial p q γ κ a → 4 ≤ x → (κ : ℝ) ≤ (1 - (q : ℝ)) * n * K / (4 * N) → (N : ℝ) ≥ 8 / γ →
      μ₀ - μ₁ ≥ γ / (4 * L)) := by sorry

end PDSEquiv
