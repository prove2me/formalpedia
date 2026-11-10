-- Prove2me | Theorems.Thm_SmallClassesNeighbourhood_Linear_minimal_diverse_restriction
-- name    : SmallClassesNeighbourhood.Linear.minimal_diverse_restriction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:35:03.745207+00:00
-- url     : https://prove2.me/theorems/ed9588c2-ad50-4120-9954-bcbc49b07f18
-- title:
--   Lemma 12 — minimally diverse restriction
-- statement:
--   Let C be a positive integer and F a bipartite graph with nonempty parts A,B. Suppose B is A-diverse and |B|≥C|A|. There exist nonempty A′⊆A and B′⊆B such that
--
--   $$B'\text{ is minimally }A'\text{-diverse},\qquad |B'|=C|A'|.$$
--
--   Minimal diversity uses strict real-ratio trace bounds on every nonempty proper subset of A′. This selects the bounded-defect restriction in the many-defects case.
--
--   Differences from the source:
--   - encoding: finite graphs and named vertex subsets → finite ambient carriers with cores on the subtype A ∪ B; reason: isolated padding is ignored; restriction to the union recovers exactly the source graph, including every uncoloured automorphism
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), Lemma 12, printed p. 8 (PDF p. 9)

import Definitions.Def_SmallClassesNeighbourhood_Linear_graphBasics

namespace SmallClassesNeighbourhood.Linear

theorem minimal_diverse_restriction {V : Type} [Fintype V] [DecidableEq V]
    (C : ℕ) (hC : 0 < C) (F : SimpleGraph V) (A B : Finset V)
    (hparts : Bipartition F A B) (hA : A.Nonempty) (hB : B.Nonempty)
    (hdiv : Diverse F A B) (hsize : C * A.card ≤ B.card) :
    ∃ A' B' : Finset V, A' ⊆ A ∧ B' ⊆ B ∧ A'.Nonempty ∧ B'.Nonempty ∧
      MinimallyDiverse F A' B' ∧ B'.card = C * A'.card := by sorry

end SmallClassesNeighbourhood.Linear
