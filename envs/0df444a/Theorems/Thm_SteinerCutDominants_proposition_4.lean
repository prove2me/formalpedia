-- Prove2me | Theorems.Thm_SteinerCutDominants_proposition_4
-- name    : SteinerCutDominants.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:52.05841+00:00
-- url     : https://prove2.me/theorems/dfe775a9-1d22-4061-8b6d-a3550e26ddde
-- title:
--   Proposition 4: gluing preserves facet inducing
-- statement:
--   If the Steiner graph $(G,T)$ is obtained by gluing two facet inducing Steiner graphs $(G_1,T_1)$ and $(G_2,T_2)$ with facet weights $c_1$ and $c_2$, respectively, then $(G,T)$ is a facet inducing Steiner graph as well, and the weights obtained from gluing $c_1$ and $c_2$ accordingly are facet weights for $(G,T)$.
--
--   Gluing is the second of the two operations. Both $T=T_1\cup T_2$ and $T=(T_1\cup T_2)\setminus\{w\}$ are covered.
--
--   Differences from the source:
--   - encoding: the weights obtained from gluing c₁ and c₂ → H carries c, and IsGluing H₁ H₂ H fixes it as the glued weights; reason: the weights are part of the weighted graph H
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, Proposition 4, p.10

import Mathlib
import Definitions.Def_SteinerCutDominants_IsFacetInducing
import Definitions.Def_SteinerCutDominants_IsGluing

namespace SteinerCutDominants

/-- **Proposition 4** (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, p.10). If
`(G, T)` is obtained by gluing two facet inducing Steiner graphs `(G₁, T₁)` and `(G₂, T₂)` with facet
weights `c₁` and `c₂`, then `(G, T)` is facet inducing and the weights obtained from gluing `c₁` and
`c₂` are facet weights for it.

**Formalization Note** `IsGluing H₁ H₂ H` carries the weights of `H` as the glued weights, and covers
both `T = T₁ ∪ T₂` and `T = (T₁ ∪ T₂) \ {w}`. -/
theorem proposition_4 (H₁ H₂ H : WSG) (h₁ : IsFacetInducing H₁) (h₂ : IsFacetInducing H₂)
    (hg : IsGluing H₁ H₂ H) : IsFacetInducing H := by sorry

end SteinerCutDominants
