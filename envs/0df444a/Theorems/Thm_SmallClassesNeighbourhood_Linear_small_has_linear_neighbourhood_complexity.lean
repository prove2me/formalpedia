-- Prove2me | Theorems.Thm_SmallClassesNeighbourhood_Linear_small_has_linear_neighbourhood_complexity
-- name    : SmallClassesNeighbourhood.Linear.small_has_linear_neighbourhood_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:35:05.715211+00:00
-- url     : https://prove2.me/theorems/46ae3d06-5122-470b-9b66-1129fc4aca0b
-- title:
--   Theorem 1 — small classes have linear neighbourhood complexity
-- statement:
--   Let C be an isomorphism-closed hereditary class of finite simple undirected graphs. Suppose there is a positive real c such that its number of labelled n-vertex graphs is at most n! c^n for every n≥1. There exists a positive real K, depending only on the class, such that every G∈C and every nonempty subset A of its vertices satisfy
--
--   $$|\{N_G(v)\cap A:v\in V(G)\}|\le K|A|.$$
--
--   Vertices in A also contribute traces, and equal traces count once. This is the paper's main theorem, with all graph orders and all positive trace-set sizes covered. It is a known mathematical result and an open formalization target.
--
--   Differences from the source:
--   - encoding: isomorphism-closed hereditary graph classes on arbitrary finite vertex sets → families on Fin n closed under every injective induced restriction; reason: every finite graph can be labelled by Fin n; bijective restrictions enforce isomorphism closure, with labels shifted by one
--   - encoding: ν_C(k)=O(k) → a single K>0 bounding every nonempty trace set; reason: the finite exceptional positive k are absorbed using the universal 2^k trace bound; the empty set is outside homogeneous linear asymptotics
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), Theorem 1, printed p. 2 (PDF p. 3)

import Definitions.Def_SmallClassesNeighbourhood_Linear_graphBasics

namespace SmallClassesNeighbourhood.Linear

theorem small_has_linear_neighbourhood_complexity (𝒞 : GraphClass) (h𝒞 : IsSmall 𝒞) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n →
      ∀ A : Finset (Fin n), A.Nonempty →
        ((traces G A Finset.univ).card : ℝ) ≤ K * (A.card : ℝ) := by sorry

end SmallClassesNeighbourhood.Linear
