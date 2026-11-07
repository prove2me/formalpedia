-- Prove2me | Theorems.Thm_PDSEquiv_lemma_5_2
-- name    : PDSEquiv.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:02:53.042675+00:00
-- url     : https://prove2.me/theorems/25526a83-150c-47b5-a5f1-cc5461135355
-- title:
--   Lemma 5.2 — low vertex-degree bound: $\|\Pi_D(L-1)\|_1=(1+o(1))\Lambda_N(k)$ uniformly over $2\le k\le N^u$
-- statement:
--   Fix $0<q<p\le1$, an integer $D\ge2$ and a constant $u<1/2$. Let $L$ be the likelihood ratio of $\mathrm{PDS}(N,k,p,q)$ against $\mathrm{ER}(N,q)$ and $\Pi_D$ the projection onto the span of the $\psi_S$ with $v(S)\le D$. Then
--   $$\|\Pi_D(L-1)\|_{1,\mathrm{ER}(N,q)}=(1+o(1))\,\Lambda_N(k)$$
--   uniformly over all integers $2\le k\le N^u$: for every $\varepsilon>0$ there is $N_0$ such that for all $N\ge N_0$ and all integers $2\le k\le N^u$,
--   $$\left|\frac{\|\Pi_D(L-1)\|_1}{\Lambda_N(k)}-1\right|\le\varepsilon.$$
--
--   The single-edge Fourier terms dominate the low vertex-degree part of the likelihood ratio, so no low vertex-degree test beats edge counting by more than a $1+o(1)$ factor.
--
--   Differences from the source:
--   - encoding: (1 + o(1)) uniformly over 2 ≤ k ≤ N^u → ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, ∀ integers 2 ≤ k ≤ N^u, |‖Π_D(L − 1)‖₁ / Λ_N(k) − 1| ≤ ε; reason: the meaning of a uniform o(1); Λ_N(k) > 0 there
--   - encoding: standing densities of §5 (Fix densities 0 < q < p ≤ 1) → real binders 0 < q < p ≤ 1; reason: the section's standing assumption
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), Lemma 5.2, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_PDSEquiv_Laws
import Definitions.Def_PDSEquiv_Fourier

set_option autoImplicit false

namespace PDSEquiv

/-- S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), Lemma 5.2, p.14 (PDF p.16).
`‖Π_D(L − 1)‖₁ = (1 + o(1)) Λ_N(k)` uniformly over all integers `2 ≤ k ≤ N^u`.

**Formalization Note.** `(1 + o(1))`, uniformly in `k`, is the explicit `∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, ∀ k`.
The norm is in `L¹(ER(N, q))`. -/
theorem lemma_5_2 (p q : ℝ) (hq : 0 < q) (hqp : q < p) (hp : p ≤ 1) (D : ℕ) (hD : 2 ≤ D) (u : ℝ)
    (hu : u < 1 / 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ k : ℕ, 2 ≤ k → (k : ℝ) ≤ (N : ℝ) ^ u →
      |erL1 q (piD q D (fun G : Graph N => likelihood N k p q G - 1)) / Lam p q N k - 1| ≤ ε := by sorry

end PDSEquiv
