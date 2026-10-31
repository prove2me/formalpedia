-- Prove2me | Theorems.Thm_SteinerCutDominants_theorem_1
-- name    : SteinerCutDominants.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:25.586235+00:00
-- url     : https://prove2.me/theorems/50859b89-f74f-45cb-9953-df8d4c3c0865
-- title:
--   Theorem 1: laminar root bases exist
-- statement:
--   If $c$ provides facet weights for the facet inducing Steiner graph $(G,T)$, then there is a **laminar root basis** for $c$: a root basis $\delta(S)$ ($S\in\mathcal L$) for $c$ with a laminar family $\mathcal L$ of subsets of $V(G)$.
--
--   This is the central structural result of the first part of the paper. It bounds the number of nonzero coefficients of a facet defining inequality.
--
--   Differences from the source: none.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, Theorem 1, p.7

import Mathlib
import Definitions.Def_SteinerCutDominants_IsFacetInducing
import Definitions.Def_SteinerCutDominants_IsRootBasis
import Definitions.Def_SteinerCutDominants_IsLaminar

namespace SteinerCutDominants

/-- **Theorem 1** (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, p.7). If `c`
provides facet weights for the facet inducing Steiner graph `(G, T)`, there is a laminar root basis
for `c`: a root basis `δ(S)` (`S ∈ 𝓛`) with `𝓛` a laminar family of subsets of `V(G)`. -/
theorem theorem_1 (H : WSG) (hH : IsFacetInducing H) :
    ∃ L : Finset (Finset H.V), IsLaminar L ∧ IsRootBasis H L := by sorry

end SteinerCutDominants
