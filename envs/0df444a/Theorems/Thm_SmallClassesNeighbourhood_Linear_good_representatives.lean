-- Prove2me | Theorems.Thm_SmallClassesNeighbourhood_Linear_good_representatives
-- name    : SmallClassesNeighbourhood.Linear.good_representatives
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:36:58.481893+00:00
-- url     : https://prove2.me/theorems/bac7f92a-bb94-404b-99e1-aa8ad95d2703
-- title:
--   Lemma 17 — many good vertices and representatives
-- statement:
--   In the standing minimal pair let C=C_0^4, |B|=C|A|, n=|A|>C^10, with C_0 sufficiently large. Let R⊆B be inclusion-maximal with A-neighbourhood distances greater than C^10. Partition A by equality of R-neighbourhoods. There are a set Q of one representative per class and B_good⊆B∖R such that
--
--   $$|B_{good}|\ge |B|/3,\qquad |N_A(v)\triangle\Sigma(v)|\le4C^{10}\quad(v\in B_{good}).$$
--
--   Here Σ(v), defined for every v∈B, is the union of classes whose representative is adjacent to v. This supplies the canonical selections used throughout the remaining proof.
--
--   Differences from the source:
--   - encoding: finite graphs and named vertex subsets → finite ambient carriers with cores on the subtype A ∪ B; reason: isolated padding is ignored; restriction to the union recovers exactly the source graph, including every uncoloured automorphism
--   - encoding: sufficiently large integer parameters → one existential positive natural threshold before every parameter and graph; reason: this is the uniform eventual meaning of sufficiently large, with no instance-dependent threshold
--   - encoding: one representative q_i in each equivalence class A_i → Q with exactly one member of each R-neighbourhood class, selected by rep; reason: this avoids choosing an enumeration of the classes and defines the identical Σ(v)
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), Lemma 17, printed p. 14 (PDF p. 15)

import Definitions.Def_SmallClassesNeighbourhood_Linear_canonical

namespace SmallClassesNeighbourhood.Linear

theorem good_representatives :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ C0 : ℕ, L ≤ C0 →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (F : SimpleGraph V) (A B R : Finset V),
      MinimalPair (C0 ^ 4) F A B → B.card = C0 ^ 4 * A.card →
      (C0 ^ 4) ^ 10 < A.card → MaximalSeparated F A B R ((C0 ^ 4) ^ 10) →
      ∃ Q Bgood : Finset V, GoodSelection (C0 ^ 4) F A B R Q Bgood := by sorry

end SmallClassesNeighbourhood.Linear
