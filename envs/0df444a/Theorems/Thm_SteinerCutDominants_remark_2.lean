-- Prove2me | Theorems.Thm_SteinerCutDominants_remark_2
-- name    : SteinerCutDominants.remark_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:27.690411+00:00
-- url     : https://prove2.me/theorems/10245bf8-6360-48b3-b0fd-412f834e75a5
-- title:
--   Remark 2: facet weights of Steiner subgraphs describe the dominant
-- statement:
--   Let $(G,T)$ be a Steiner graph.
--
--   1. For $b>0$, the inequality $ax\ge b$ defines a facet of $\mathrm{CUT}_+(G,T)$ if and only if $a$ and $b$ are a positive multiple $r$ of $(c,\gamma_c)$ for facet weights $c$ of a facet inducing Steiner subgraph $(G_a,T)$ of $(G,T)$.
--   2. $\mathrm{CUT}_+(G,T)$ is the set of $x\ge 0$ satisfying every such inequality.
--
--   This is the reason the paper studies facet inducing Steiner graphs: an inequality description of the dominant is obtained from all facet weights of all facet inducing Steiner subgraphs.
--
--   Differences from the source:
--   - reading: "it suffices … to find all facet weights for all facet inducing Steiner subgraphs" → the two precise claims (1) and (2); reason: an informal sentence; this is the strongest reading, and the one the page uses in the proof of Theorem 5
--   - encoding: facet inducing Steiner subgraph of (G, T) → H with an embedding φ and scale r, IsSupportRep G T a H φ r; reason: a real vector is compared with the subgraph up to scale
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, Remark 2, p.5

import Mathlib
import Definitions.Def_SteinerCutDominants_DefinesFacet
import Definitions.Def_SteinerCutDominants_IsFacetInducing
import Definitions.Def_SteinerCutDominants_IsSupportRep
import Definitions.Def_SteinerCutDominants_gamma

open Matrix

namespace SteinerCutDominants

/-- **Remark 2** (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, p.5). The facet
weights of the facet inducing Steiner subgraphs of `(G, T)` determine an inequality description of
`CUT₊(G, T)`: the facet defining inequalities with positive right-hand side are exactly the scaled
facet weights of those subgraphs, and with the nonnegativity constraints they describe the
dominant.

**Formalization Note** The page's "it suffices" is read as these two precise claims. A Steiner
subgraph `(G_a, T)` is given by `IsSupportRep`. -/
theorem remark_2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hG : G.Connected) (hT : 2 ≤ T.card) :
    (∀ (a : G.edgeSet → ℝ) (b : ℝ), 0 < b →
      (DefinesFacet G T a b ↔
        ∃ (H : WSG) (φ : H.V ↪ V) (r : ℝ), 0 < r ∧ IsSupportRep G T a H φ r ∧
          b = r * gamma H ∧ IsFacetInducing H)) ∧
    cutDominant G T =
      {x | 0 ≤ x ∧ ∀ (a : G.edgeSet → ℝ) (b : ℝ), 0 < b → DefinesFacet G T a b → b ≤ a ⬝ᵥ x} := by sorry

end SteinerCutDominants
