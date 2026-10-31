-- Prove2me | Theorems.Thm_SteinerCutDominants_theorem_3
-- name    : SteinerCutDominants.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:55.955854+00:00
-- url     : https://prove2.me/theorems/49a831a8-4a04-4ff4-80b5-819131703286
-- title:
--   Theorem 3: splitting at a cut node
-- statement:
--   Let $(G,T)$ be a facet inducing Steiner graph with facet weights $c$, and let $w\in V(G)$ be a cut node of $G$. Let $V_1\subseteq V(G)$ be the node set of one of the components of $G\setminus w$ and $V_2:=V(G\setminus w)\setminus V_1$. Denote by $G_1$ and $G_2$ the subgraphs of $G$ induced by $V_1\cup\{w\}$ and $V_2\cup\{w\}$, and let $T_1=(T\cap V_1)\cup\{w\}$, $T_2=(T\cap V_2)\cup\{w\}$.
--
--   Then $|T_1|,|T_2|\ge 2$, and both $(G_1,T_1)$ and $(G_2,T_2)$ are facet inducing Steiner graphs with facet weights $c_1$ and $c_2$ that are the minimum integer forms of the restrictions of $c$ to $E(G_1)$ and $E(G_2)$.
--
--   Note that $(G,T)$ can be obtained by gluing $(G_1,T_1)$ and $(G_2,T_2)$ at their common terminal node $w$, and $c$ is the weight vector obtained by gluing $c_1$ and $c_2$ accordingly.
--
--   This is the inverse of Proposition 4.
--
--   Differences from the source:
--   - encoding: |T₁|, |T₂| ≥ 2 and the pieces are Steiner graphs → H₁, H₂ : WSG, which bundle both; reason: WSG carries connectivity and 2 ≤ |T|
--   - encoding: minimum integer forms of the restrictions of c → IsBlock (restriction = r · cᵢ, r > 0) with gcd cᵢ = 1 from IsFacetInducing; reason: the definition of minimum integer form
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, Theorem 3, p.10

import Mathlib
import Definitions.Def_SteinerCutDominants_IsFacetInducing
import Definitions.Def_SteinerCutDominants_IsCutNode
import Definitions.Def_SteinerCutDominants_IsBlock
import Definitions.Def_SteinerCutDominants_IsGluingAt

namespace SteinerCutDominants

/-- **Theorem 3** (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, p.10). Let `(G, T)`
be facet inducing with facet weights `c`, `w` a cut node of `G`, `V₁` the node set of a component of
`G \ w`, `V₂ := V(G \ w) \ V₁`, `G₁`, `G₂` the subgraphs induced by `V₁ ∪ {w}`, `V₂ ∪ {w}`, and
`T₁ = (T ∩ V₁) ∪ {w}`, `T₂ = (T ∩ V₂) ∪ {w}`. Then `|T₁|, |T₂| ≥ 2`, and both `(G₁, T₁)`, `(G₂, T₂)`
are facet inducing with facet weights the minimum integer forms of the restrictions of `c`. Note
that `(G, T)` is obtained by gluing them at `w`, and `c` by gluing `c₁` and `c₂`.

**Formalization Note** `|T₁|, |T₂| ≥ 2` and connectivity of `G₁`, `G₂` are bundled in `H₁, H₂ : WSG`.
The pieces are given by `IsBlock`, which fixes them up to isomorphism. -/
theorem theorem_3 (H : WSG) (hH : IsFacetInducing H) (w : H.V) (hw : IsCutNode H.G w)
    (C : (H.G.induce ({w}ᶜ : Set H.V)).ConnectedComponent) :
    ∃ (H₁ H₂ : WSG) (φ₁ : H₁.V ↪ H.V) (φ₂ : H₂.V ↪ H.V),
      IsBlock H w (Subtype.val '' C.supp) H₁ φ₁ ∧
      IsBlock H w (({w}ᶜ : Set H.V) \ (Subtype.val '' C.supp)) H₂ φ₂ ∧
      IsFacetInducing H₁ ∧ IsFacetInducing H₂ ∧ IsGluingAt H₁ H₂ H φ₁ φ₂ w := by sorry

end SteinerCutDominants
