-- Prove2me | Theorems.Thm_SteinerCutDominants_proposition_3
-- name    : SteinerCutDominants.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:18:59.129463+00:00
-- url     : https://prove2.me/theorems/0e8094dc-aee0-4e8f-82ba-42b432147736
-- title:
--   Proposition 3: subdivision preserves facet inducing
-- statement:
--   If the Steiner graph $(G,T)$ is obtained by subdivision from a facet inducing Steiner graph $(G',T')$ with facet weights $c'$, then also $(G,T)$ is a facet inducing Steiner graph, with facet weights $c$ obtained by subdividing $c'$ accordingly.
--
--   This is the first of the two operations that build facet inducing Steiner graphs.
--
--   Differences from the source:
--   - encoding: facet weights c obtained by subdividing c′ → H carries c, and IsSubdivision H′ H fixes it as the subdivided c′; reason: the weights are part of the weighted graph H
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, Proposition 3, p.8

import Mathlib
import Definitions.Def_SteinerCutDominants_IsFacetInducing
import Definitions.Def_SteinerCutDominants_IsSubdivision

namespace SteinerCutDominants

/-- **Proposition 3** (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, p.8). If
`(G, T)` is obtained by subdivision from a facet inducing Steiner graph `(G', T')` with facet weights
`c'`, then `(G, T)` is facet inducing with the facet weights `c` obtained by subdividing `c'`
accordingly.

**Formalization Note** `IsSubdivision H' H` carries the weights of `H` as the subdivided `c'`. -/
theorem proposition_3 (H' H : WSG) (hH' : IsFacetInducing H') (hs : IsSubdivision H' H) :
    IsFacetInducing H := by sorry

end SteinerCutDominants
