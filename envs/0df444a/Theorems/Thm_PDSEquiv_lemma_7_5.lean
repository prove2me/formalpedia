-- Prove2me | Theorems.Thm_PDSEquiv_lemma_7_5
-- name    : PDSEquiv.lemma_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:02:57.006197+00:00
-- url     : https://prove2.me/theorems/9f34b43c-0efb-4a42-8cd9-89289fed90f7
-- title:
--   Lemma 7.5 — concentration of vertex scores given $\mathbf 1\{v\in C\}=s$
-- statement:
--   Fix rationals $0<q<p\le1$, integers $1\le n\le N-1$, real $K\in[1,N-1]$ and a distinguisher $O$ on $n$-vertex graphs. For each $v\in[N]$, $s\in\{0,1\}$ and $t\ge0$,
--   $$\Pr_{G,C}\bigl[|Z_v(G)-\mu_s|\ge t\ \big|\ \mathbf 1\{v\in C\}=s\bigr]\le2\exp\Bigl(-\frac{2t^2(N-1)L(1-\theta)}n\Bigr),$$
--   the probability being over $(G,C)\sim\widetilde{\mathrm{PDS}}(N,K,p,q)$ conditional on $\mathbf 1\{v\in C\}=s$; the level and the internal randomness of $\mathrm{Thin}_n$ and $O$ are averaged out in $Z_v(G)$.
--
--   Each vertex score concentrates around the mean of its class, so a threshold between $\mu_1$ and $\mu_0$ classifies all vertices at once.
--
--   Differences from the source:
--   - encoding: standing assumptions of §7.1 → binders 1 ≤ n ≤ N − 1, 1 ≤ K ≤ N − 1, rationals 0 < q < p ≤ 1; κ, γ and (8) omitted; reason: the lemma does not use κ, γ or (8)
--   - encoding: a randomized distinguisher O on n-vertex graphs → its acceptance function a : G_n → [0, 1]; reason: Z_v and μ_s depend on O only through a
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), Lemma 7.5, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_PDSEquiv_Laws
import Definitions.Def_PDSEquiv_Thin

set_option autoImplicit false

namespace PDSEquiv

/-- S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), Lemma 7.5, p.28 (PDF p.30).
Concentration of vertex scores, conditional on `1{v ∈ C} = s`, over `(G, C) ∼ P̃DS(N, K, p, q)`.

**Formalization Note.** The standing assumptions of §7.1 are binders, except `κ`, `γ` and (8), which
this lemma does not use. `s : Bool` is the bit `s ∈ {0, 1}`. -/
theorem lemma_7_5 (p q : ℚ) (hq : 0 < q) (hqp : q < p) (hp : p ≤ 1) (N n : ℕ) (hn : 1 ≤ n)
    (hnN : n + 1 ≤ N) (K : ℝ) (hK : 1 ≤ K) (hKN : K ≤ (N : ℝ) - 1) (a : Graph n → ℝ)
    (ha : ∀ H, 0 ≤ a H ∧ a H ≤ 1) (v : Fin N) (s : Bool) (t : ℝ) (ht : 0 ≤ t) :
    condProb K p q v s (fun G _ => t ≤ |scoreZ p q a G v - condMean K p q a v s|)
      ≤ 2 * Real.exp (-(2 * t ^ 2 * ((N : ℝ) - 1) * levelL p q N * (1 - theta p q)) / n) := by sorry

end PDSEquiv
