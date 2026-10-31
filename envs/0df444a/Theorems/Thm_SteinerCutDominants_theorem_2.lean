-- Prove2me | Theorems.Thm_SteinerCutDominants_theorem_2
-- name    : SteinerCutDominants.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:31.432453+00:00
-- url     : https://prove2.me/theorems/e17192fa-8cd9-4aa6-8675-5a6cfc5c0cbc
-- title:
--   Theorem 2: reducing a non-terminal node of degree two
-- statement:
--   Let $(G,T)$ be a facet inducing Steiner graph with facet weights $c$, and let $w\in V(G)\setminus T$ be a non-terminal node with exactly two neighbors $u$ and $v$. Then:
--
--   1. $c(uw)=c(vw)$, and $u$ and $v$ are not adjacent.
--   2. If $G'$ is obtained from $G$ by reducing $w$, then $(G',T')$ with $T'=T$ is a facet inducing Steiner graph with facet weights $c'$ obtained from $c$ by setting $c'(uv)=c(uw)=c(vw)$ and $c'(e)=c(e)$ for all other edges.
--
--   Note that $(G,T)$ can be obtained from $(G',T')$ by subdivision of the edge $uv$, and $c$ is the weight vector obtained by subdividing $c'$ accordingly.
--
--   This is the inverse of Proposition 3.
--
--   Differences from the source:
--   - encoding: G′ obtained from G by reducing w, with the stated c′, and the Note → H′ with IsSubdivisionAt H′ H w; such H′ exists and each is facet inducing; reason: the relation is both the reduction and the Note, up to isomorphism
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, Theorem 2, p.9

import Mathlib
import Definitions.Def_SteinerCutDominants_IsFacetInducing
import Definitions.Def_SteinerCutDominants_IsSubdivisionAt

namespace SteinerCutDominants

/-- **Theorem 2** (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, p.9). Let `(G, T)`
be facet inducing with facet weights `c`, and let `w ∉ T` have exactly two neighbors `u`, `v`. Then
(1) `c(uw) = c(vw)` and `u`, `v` are not adjacent; (2) reducing `w` gives a graph `(G', T')`,
`T' = T`, that is facet inducing with the weights `c'(uv) = c(uw) = c(vw)` and `c'(e) = c(e)`
otherwise. Note that `(G, T)` is obtained from `(G', T')` by subdivision of `uv`, and `c` by
subdividing `c'`.

**Formalization Note** `IsSubdivisionAt H' H w` is the page's "reducing `w`" and at once its Note. The
reduction exists (clause `∃`), and every reduction is facet inducing (clause `∀`). -/
theorem theorem_2 (H : WSG) (hH : IsFacetInducing H) (w u v : H.V) (hw : w ∉ H.T) (huv : u ≠ v)
    (hN : ∀ x, H.G.Adj w x ↔ x = u ∨ x = v) :
    H.wt u w = H.wt v w ∧ ¬ H.G.Adj u v ∧
      (∃ H' : WSG, IsSubdivisionAt H' H w) ∧
      ∀ H' : WSG, IsSubdivisionAt H' H w → IsFacetInducing H' := by sorry

end SteinerCutDominants
