-- Prove2me | Theorems.Thm_SteinerCutDominants_facetInducing_iff_definesFacet
-- name    : SteinerCutDominants.facetInducing_iff_definesFacet
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:17.510988+00:00
-- url     : https://prove2.me/theorems/507e5e5c-dd24-4cb3-b787-7393a9c18e52
-- title:
--   Facet weights are the full-support facets in minimum integer form
-- statement:
--   For a weighted Steiner graph $((G,T),c)$, the following are equivalent: $c$ provides facet weights for $(G,T)$ in the sense of `IsFacetInducing` (positive, minimum integer form, root basis); and $c$ is all-positive, in minimum integer form, $\gamma=\gamma_c(G,T)>0$, and $cx\ge\gamma$ defines a facet of $\mathrm{CUT}_+(G,T)$.
--
--   The second description is the paper's definition, and the first is the characterization stated right after it "due to Remark 1".
--
--   Differences from the source:
--   - encoding: G_c = G → every edge has positive weight; reason: G is connected with at least two terminals, so it has no isolated node and V_c = V(G)
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §2, p.4

import Mathlib
import Definitions.Def_SteinerCutDominants_DefinesFacet
import Definitions.Def_SteinerCutDominants_IsFacetInducing
import Definitions.Def_SteinerCutDominants_gamma

namespace SteinerCutDominants

/-- The page's definition of facet weights (Conforti, Kaibel, *Steiner Cut Dominants*,
arXiv:2209.14802v2, §2, p.4): `c` provides facet weights for `(G, T)` exactly when `c x ≥ γ`, in
minimum integer form, defines a facet of `CUT₊(G, T)` with `G_c = G` and `γ = γ_c(G, T) > 0`. -/
theorem facetInducing_iff_definesFacet (H : WSG) :
    IsFacetInducing H ↔
      (∀ e, 0 < H.c e) ∧ (Finset.univ : Finset H.G.edgeSet).gcd H.c = 1 ∧ 0 < gamma H ∧
        DefinesFacet H.G H.T H.wR (gamma H) := by sorry

end SteinerCutDominants
