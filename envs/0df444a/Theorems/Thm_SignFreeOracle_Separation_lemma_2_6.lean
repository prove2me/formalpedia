-- Prove2me | Theorems.Thm_SignFreeOracle_Separation_lemma_2_6
-- name    : SignFreeOracle.Separation.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:52.572491+00:00
-- url     : https://prove2.me/theorems/c954725a-bb92-4db0-ab21-a23bdb6a9e4c
-- title:
--   Lemma 2.6 — average Moore bound
-- statement:
--   Let $G$ be a nonempty finite simple graph, let $g$ be a natural girth lower bound, and let the real number $d\ge2$ be a lower bound for its average degree. Then
--   $$|V(G)|\ge(d-1)^{\lfloor(g-1)/2\rfloor}.$$
--   Girth is measured by actual cycles; an acyclic graph has infinite girth. The integer exponent is truncated only for $g=0$, when the bound is simply nonemptiness. The hypothesis is on average degree, not on minimum degree or regularity. This is the size obstruction used in the closure argument.
--
--   Differences from the source:
--   - generalization: g is the graph girth → g is any natural lower bound on all cycle lengths; reason: the conclusion with the actual finite girth is included, and forests have infinite girth
--   - encoding: finite graphs, labellings and quantum registers → finite vertex carriers, numerical labellings and complex amplitude functions; reason: these are equivalent finite representations; numerical neighbour positions are zero-based
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Lemma 2.6, p. 8 (PDF p. 8)

import Definitions.Def_SignFreeOracle_Separation_Graph

set_option autoImplicit false

namespace SignFreeOracle.Separation

theorem lemma_2_6 {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (g : ℕ) (d : ℝ) (hg : GirthAtLeast G g) (hd : 2 ≤ d)
    (havg : d ≤ avgDegree G) :
    (d - 1) ^ ((g - 1) / 2) ≤ (Fintype.card V : ℝ) := by sorry

end SignFreeOracle.Separation
