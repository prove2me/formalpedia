-- Prove2me | Theorems.Thm_RandOrderCSP_lemma_5_11
-- name    : RandOrderCSP.lemma_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:08:24.965862+00:00
-- url     : https://prove2.me/theorems/4a058c28-2d2f-45cf-865b-ded10b8648f3
-- title:
--   Lemma 5.11 — acyclicity estimate
-- statement:
--   For every $k\ge2$ and every $k$-uniform hypergraph $G_*$, there are $\alpha_0>0$ and $C<\infty$ such that for every $n\ge1$ and $0<\alpha\le\alpha_0$, if $H\sim\mathrm{Poi}(G_*^n,\alpha n^{-(k-1)})$ then
--
--   $$\mathbb P[\mathrm{Acy}(H)]\ge1-C\alpha^2.$$
--
--   The restriction $T\alpha^2\le c$ of the DIHP lower bound uses this to make all players' hypergraphs acyclic.
--
--   Differences from the source: none.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), Lemma 5.11, p.24

import Mathlib
import Definitions.Def_RandOrderCSP_compPartition
import Definitions.Def_RandOrderCSP_blowup
import Definitions.Def_RandOrderCSP_poiLaw

namespace RandOrderCSP

/-- **Lemma 5.11 (acyclicity estimate).** Singer, Tulsiani, Velusamy, *A dichotomy theorem for
approximating CSPs in random-order streams*, STOC 2027 submission (manuscript sha256 3aca9d2f…),
Lemma 5.11, p.24.

**Formalization Note.** `H ∼ Poi(G∗^n, αn^{-(k-1)})` is `sparsify (blowup G n) c` for a count vector
`c ∼ poiLaw`. -/
theorem lemma_5_11 {k : ℕ} (hk : 2 ≤ k) {V E : Type} [Fintype V] [Nonempty V] [Fintype E]
    (G : Hypergraph k V E) :
    ∃ α₀ C : ℝ, 0 < α₀ ∧ ∀ n : ℕ, 1 ≤ n → ∀ α : ℝ, 0 < α → α ≤ α₀ →
      1 - C * α ^ 2 ≤
        (poiLaw (E × (Fin k → Fin n)) (poiRate α n k)
          {c | (sparsify (blowup G n) c).Acy}).toReal := by sorry

end RandOrderCSP
