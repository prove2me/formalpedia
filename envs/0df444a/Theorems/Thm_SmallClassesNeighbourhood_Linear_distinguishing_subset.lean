-- Prove2me | Theorems.Thm_SmallClassesNeighbourhood_Linear_distinguishing_subset
-- name    : SmallClassesNeighbourhood.Linear.distinguishing_subset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:35:05.089763+00:00
-- url     : https://prove2.me/theorems/bc04eef3-a192-4d68-8dcd-59aa46cd7e75
-- title:
--   Lemma 11 — a small mutually distinguishing subset
-- statement:
--   Let F be bipartite with nonempty parts A,B, and suppose B is A-diverse. There exists A′⊆A satisfying
--
--   $$|A'|\le|B|-1,\qquad B\text{ is }A'\text{-diverse},\qquad A'\text{ is }B\text{-diverse}.$$
--
--   The last, dual, diversity condition is part of the conclusion. For |B|=1, the allowed choice A′=∅ gives both conclusions. This result supplies distinguishing sets and witnesses in the core constructions.
--
--   Differences from the source:
--   - encoding: finite graphs and named vertex subsets → finite ambient carriers with cores on the subtype A ∪ B; reason: isolated padding is ignored; restriction to the union recovers exactly the source graph, including every uncoloured automorphism
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), Lemma 11, printed p. 8 (PDF p. 9)

import Definitions.Def_SmallClassesNeighbourhood_Linear_graphBasics

namespace SmallClassesNeighbourhood.Linear

theorem distinguishing_subset {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (A B : Finset V) (hparts : Bipartition F A B)
    (hA : A.Nonempty) (hB : B.Nonempty) (hdiv : Diverse F A B) :
    ∃ A' : Finset V, A' ⊆ A ∧ A'.card ≤ B.card - 1 ∧ Diverse F A' B ∧ Diverse F B A'  := by sorry

end SmallClassesNeighbourhood.Linear
