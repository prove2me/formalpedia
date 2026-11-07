-- Prove2me | Theorems.Thm_PDSEquiv_lemma_5_4
-- name    : PDSEquiv.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:02:34.632207+00:00
-- url     : https://prove2.me/theorems/f2dc53ec-cd33-4a3b-ac5b-345d05c80a87
-- title:
--   Lemma 5.4 — embedding: $T_{n,N}$ preserves planted means and contracts $\|g\|_2$ by $(n/N)^{(D+1)/2}$ when $\Pi_Dg=0$
-- statement:
--   Fix $0<q<p\le1$. Let $1\le n\le N$ and $g\in L^2(\mathrm{ER}(N,q))$. For every $0\le k\le n$,
--   $$\mathbb E_{G\sim\mathrm{PDS}(n,k,p,q)}\bigl[(T_{n,N}g)(G)\bigr]=\mathbb E_{Y\sim\mathrm{PDS}(N,k,p,q)}[g(Y)].$$
--   If $\Pi_Dg=0$ for an integer $D\ge2$, then
--   $$\|T_{n,N}g\|_{2,\mathrm{ER}(n,q)}\le\Bigl(\frac nN\Bigr)^{(D+1)/2}\|g\|_{2,\mathrm{ER}(N,q)}.$$
--
--   The embedding transfers planted expectations to a smaller graph while shrinking the null-model norm of a high vertex-degree function.
--
--   Differences from the source:
--   - encoding: standing densities of §5 → real binders 0 < q < p ≤ 1; reason: the section's standing assumption
--   - encoding: g ∈ L²(ER(N, q)) → any g : G_N → ℝ; reason: ER(N, q) has full support for 0 < q < 1, so L² is all functions
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), Lemma 5.4, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_PDSEquiv_Laws
import Definitions.Def_PDSEquiv_Fourier
import Definitions.Def_PDSEquiv_Embed

set_option autoImplicit false

namespace PDSEquiv

/-- S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), Lemma 5.4, p.15 (PDF p.17).
The embedding operator preserves planted means, and contracts the `L²` norm of a function with
`Π_D g = 0` by `(n/N)^{(D+1)/2}`. -/
theorem lemma_5_4 (p q : ℝ) (hq : 0 < q) (hqp : q < p) (hp : p ≤ 1) (n N : ℕ) (hn : 1 ≤ n)
    (hnN : n ≤ N) (g : Graph N → ℝ) :
    (∀ k : ℕ, k ≤ n →
      expect (pdsMass n k p q) (embedT q g) = expect (pdsMass N k p q) g) ∧
    (∀ D : ℕ, 2 ≤ D → piD q D g = 0 →
      erL2 q (embedT (n := n) q g) ≤ ((n : ℝ) / N) ^ (((D : ℝ) + 1) / 2) * erL2 q g) := by sorry

end PDSEquiv
