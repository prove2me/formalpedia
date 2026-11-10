-- Prove2me | Theorems.Thm_SmallClassesNeighbourhood_Linear_bounded_neighbourhood_core
-- name    : SmallClassesNeighbourhood.Linear.bounded_neighbourhood_core
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:35:15.195192+00:00
-- url     : https://prove2.me/theorems/a26c86b8-2abe-4048-aa4d-7cb36414bf6a
-- title:
--   Lemma 14 — bounded-neighbourhood automorphism core
-- statement:
--   For all sufficiently large integers C,C′, let F be bipartite with parts A,B. Suppose B is minimally A-diverse, |B|=C|A|, and every v∈B has |N_A(v)|≤C′. There exists B′⊆B such that
--
--   $$|B'|\le|A|-1,\qquad |Aut(F[A,B'])|\le\max\{C,C'\}^{4|A|}.$$
--
--   A is nonempty by minimal diversity, so natural subtraction agrees with |A|−1. All uncoloured automorphisms are counted. This supplies a core when one side has bounded neighbourhood sizes.
--
--   Differences from the source:
--   - encoding: finite graphs and named vertex subsets → finite ambient carriers with cores on the subtype A ∪ B; reason: isolated padding is ignored; restriction to the union recovers exactly the source graph, including every uncoloured automorphism
--   - encoding: sufficiently large integer parameters → one existential positive natural threshold before every parameter and graph; reason: this is the uniform eventual meaning of sufficiently large, with no instance-dependent threshold
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), Lemma 14, printed p. 9 (PDF p. 10)

import Definitions.Def_SmallClassesNeighbourhood_Linear_graphBasics

namespace SmallClassesNeighbourhood.Linear

theorem bounded_neighbourhood_core :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ C C' : ℕ, L ≤ C → L ≤ C' →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (F : SimpleGraph V) (A B : Finset V),
      Bipartition F A B → MinimallyDiverse F A B → B.card = C * A.card →
      (∀ v ∈ B, (trace F A v).card ≤ C') →
      ∃ B' : Finset V, B' ⊆ B ∧ B'.card ≤ A.card - 1 ∧
        autCount F A B' ≤ (max C C') ^ (4 * A.card) := by sorry

end SmallClassesNeighbourhood.Linear
