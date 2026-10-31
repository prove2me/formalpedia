-- Prove2me | Theorems.Thm_SteinerCutDominants_remark_3
-- name    : SteinerCutDominants.remark_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:10.031101+00:00
-- url     : https://prove2.me/theorems/7cab5b3e-ba6e-47c7-a17f-a209b83d16f9
-- title:
--   Remark 3: constructability from irreducible Steiner graphs
-- statement:
--   A weighted Steiner graph $(G,T)$ is facet inducing if and only if it is constructable from irreducible facet inducing weighted Steiner graphs, each of which then has at most $|T|$ terminals.
--
--   Constructability here is the page's linear notion: each step subdivides the current graph or glues it with a member of the family.
--
--   The equivalence is stated with the family of all irreducible facet inducing weighted Steiner graphs; the parenthesis is stated as: whenever $(G,T)$ is constructable from a family $\mathcal F$ of irreducible graphs, it is constructable from the members of $\mathcal F$ with at most $|T|$ terminals.
--
--   Differences from the source:
--   - encoding: "(each of which then has at most |T| terminals)" → every construction of (G, T) from a family F of irreducible graphs can be carried out with the members of F having at most |T| terminals; reason: Constructable is a proposition that keeps no record of the members a construction uses
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, Remark 3, p.11

import Mathlib
import Definitions.Def_SteinerCutDominants_IsIrreducible
import Definitions.Def_SteinerCutDominants_Constructable

namespace SteinerCutDominants

/-- **Remark 3** (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, p.11). A weighted
Steiner graph `(G, T)` is facet inducing if and only if it is constructable from irreducible facet
inducing weighted Steiner graphs, each of which then has at most `|T|` terminals.

**Formalization Note** `Constructable` keeps no record of the members a construction uses, so "each
of which then has at most `|T|` terminals" is stated as: whenever `K` is constructable from a family
`F` of irreducible graphs, it is constructable from the members of `F` with at most `|T|`
terminals. -/
theorem remark_3 (K : WSG) :
    (IsFacetInducing K ↔ Constructable {H | IsIrreducible H} K) ∧
      ∀ F : Set WSG, (∀ H ∈ F, IsIrreducible H) → Constructable F K →
        Constructable {H | H ∈ F ∧ H.T.card ≤ K.T.card} K := by sorry

end SteinerCutDominants
