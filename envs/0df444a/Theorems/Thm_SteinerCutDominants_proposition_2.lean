-- Prove2me | Theorems.Thm_SteinerCutDominants_proposition_2
-- name    : SteinerCutDominants.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:20.604284+00:00
-- url     : https://prove2.me/theorems/98811a22-17b6-4bbc-a004-7906c82ae269
-- title:
--   Proposition 2: minimal sets of a laminar root basis are terminals
-- statement:
--   Let $\delta(S)$ ($S\in\mathcal L$) be a laminar root basis for facet weights $c$ of a facet inducing Steiner graph $(G,T)$. Then $\mathcal L_{\min}$ consists of singletons $\{t\}$ with $t\in T$.
--
--   Consequently $|\mathcal L_{\min}|\le|T|$, which combined with Lemma 1 bounds the size of the basis in terms of $|V(G)|$ and $|T|$.
--
--   Differences from the source: none.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, Proposition 2, p.7

import Mathlib
import Definitions.Def_SteinerCutDominants_IsFacetInducing
import Definitions.Def_SteinerCutDominants_IsRootBasis
import Definitions.Def_SteinerCutDominants_IsLaminar
import Definitions.Def_SteinerCutDominants_lminOf

namespace SteinerCutDominants

/-- **Proposition 2** (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, p.7). Let
`δ(S)` (`S ∈ 𝓛`) be a laminar root basis for facet weights `c` of a facet inducing Steiner graph
`(G, T)`. Then `𝓛_min` consists of singleton elements that are in `T`. -/
theorem proposition_2 (H : WSG) (hH : IsFacetInducing H) (L : Finset (Finset H.V))
    (hL : IsLaminar L) (hB : IsRootBasis H L) :
    ∀ S ∈ lminOf L, ∃ t ∈ H.T, S = {t} := by sorry

end SteinerCutDominants
