-- Prove2me | Theorems.Thm_SteinerCutDominants_lemma_4
-- name    : SteinerCutDominants.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:12.739605+00:00
-- url     : https://prove2.me/theorems/62d227af-649d-4da9-88f0-0fdc2ab74eaf
-- title:
--   Lemma 4: uncrossing two roots
-- statement:
--   Let $\delta(S_1)$ and $\delta(S_2)$ be roots of the facet weights $c$ of the facet inducing Steiner graph $(G,T)$. Then at least one of the following holds, as equations of incidence vectors:
--
--   1. $\delta(S_1\cap S_2)$ and $\delta(S_1\cup S_2)$ are both roots and
--   $$\delta(S_1)+\delta(S_2)=\delta(S_1\cap S_2)+\delta(S_1\cup S_2);$$
--   2. $\delta(S_1\setminus S_2)$ and $\delta(S_2\setminus S_1)$ are both roots and
--   $$\delta(S_1)+\delta(S_2)=\delta(S_1\setminus S_2)+\delta(S_2\setminus S_1).$$
--
--   Which alternative applies depends on where the terminals lie. Both are needed, since a $T$-Steiner cut need not stay one under intersection and union.
--
--   Differences from the source: none.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, Lemma 4, p.7

import Mathlib
import Definitions.Def_SteinerCutDominants_IsFacetInducing
import Definitions.Def_SteinerCutDominants_IsRoot

namespace SteinerCutDominants

/-- **Lemma 4** (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, p.7). If `δ(S₁)` and
`δ(S₂)` are roots of the facet weights `c` of `(G, T)`, then `δ(S₁ ∩ S₂)` and `δ(S₁ ∪ S₂)` are both
roots with `δ(S₁) + δ(S₂) = δ(S₁ ∩ S₂) + δ(S₁ ∪ S₂)`, or `δ(S₁ \ S₂)` and `δ(S₂ \ S₁)` are both
roots with `δ(S₁) + δ(S₂) = δ(S₁ \ S₂) + δ(S₂ \ S₁)`, as incidence vectors. -/
theorem lemma_4 (H : WSG) (hH : IsFacetInducing H) (S₁ S₂ : Finset H.V) (h₁ : IsRoot H S₁)
    (h₂ : IsRoot H S₂) :
    (IsRoot H (S₁ ∩ S₂) ∧ IsRoot H (S₁ ∪ S₂) ∧
      cutVec H.G S₁ + cutVec H.G S₂ = cutVec H.G (S₁ ∩ S₂) + cutVec H.G (S₁ ∪ S₂)) ∨
    (IsRoot H (S₁ \ S₂) ∧ IsRoot H (S₂ \ S₁) ∧
      cutVec H.G S₁ + cutVec H.G S₂ = cutVec H.G (S₁ \ S₂) + cutVec H.G (S₂ \ S₁)) := by sorry

end SteinerCutDominants
