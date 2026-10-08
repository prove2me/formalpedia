-- Prove2me | Theorems.Thm_StrongPerfectGraph_OddPrism_no_anticonnected_breaking_set
-- name    : StrongPerfectGraph.OddPrism.no_anticonnected_breaking_set
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:30:29.796654+00:00
-- url     : https://prove2.me/theorems/a059c442-b393-4f53-9adc-a227035d06bd
-- title:
--   11.4, pp. 129–130 — no anticonnected set separates a right-star from the strip
-- statement:
--   Let $G$ be a Berge graph with no appearance of $K_4$ and no even prism, and let $S=(A,C,B)$ be a step-connected strip in $G$. Let $F\subseteq V(G)\setminus(A\cup B\cup C)$ be connected, with no edges between $F$ and $A\cup B\cup C$. Then there is **no** anticonnected set $Q\subseteq V(G)\setminus(A\cup B\cup C\cup F)$ such that all of the following hold:
--
--   1. some right-star has a neighbour in $F$ and a nonneighbour in $Q$;
--   2. some vertex of $B$ has a nonneighbour in $Q$;
--   3. some left-star with a neighbour in $F$ is $Q$-complete;
--   4. every vertex of $Q$ has a neighbour in $F$;
--   5. every vertex of $Q$ has a neighbour in $A\cup B\cup C$;
--   6. no vertex of $Q$ is a left-star.
--
--   This is the key step in the proof of 11.5 that 1-breakers force balanced skew partitions.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), pp. 129–130, 11.4

import Mathlib
import Definitions.Def_StrongPerfectGraph_OddPrism_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_IsProperTwoJoin
import Definitions.Def_StrongPerfectGraph_OddPrism_AppearsIn
import Definitions.Def_StrongPerfectGraph_OddPrism_IsPrism
import Definitions.Def_StrongPerfectGraph_OddPrism_IsStepConnectedStrip
import Definitions.Def_StrongPerfectGraph_OddPrism_IsStaircase

namespace StrongPerfectGraph.OddPrism

/-- **11.4** (pp. 129–130). Let `G` be a Berge graph with no appearance of `K₄` and no even
prism, let `S = (A, C, B)` be a step-connected strip in `G`, and let `F ⊆ V(G) \ (A ∪ B ∪ C)`
be connected with no edges between `F` and `A ∪ B ∪ C`. Then there is no anticonnected
`Q ⊆ V(G) \ (A ∪ B ∪ C ∪ F)` such that: some right-star has a neighbour in `F` and a
nonneighbour in `Q`; some vertex of `B` has a nonneighbour in `Q`; some left-star with a
neighbour in `F` is `Q`-complete; every vertex of `Q` has a neighbour in `F`; every vertex
of `Q` has a neighbour in `A ∪ B ∪ C`; and no vertex of `Q` is a left-star. -/
theorem no_anticonnected_breaking_set {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsBerge G) (hK4 : ¬ AppearsIn K4 G)
    (hprism : ¬ ContainsEvenPrism G)
    (A C B : Set V) (hS : IsStepConnected G A C B)
    (F : Set V) (hFS : F ⊆ (A ∪ B ∪ C)ᶜ) (hFconn : StrongPerfectGraph.Main.IsConnectedSet G F)
    (hFedges : ∀ f ∈ F, ∀ s ∈ A ∪ B ∪ C, ¬ G.Adj f s) :
    ¬ ∃ Q : Set V, Q ⊆ (A ∪ B ∪ C ∪ F)ᶜ ∧ StrongPerfectGraph.Main.IsConnectedSet Gᶜ Q ∧
      (∃ u, IsRightStar G A C B u ∧ (∃ f ∈ F, G.Adj u f) ∧ ∃ q ∈ Q, ¬ G.Adj u q) ∧
      (∃ b ∈ B, ∃ q ∈ Q, ¬ G.Adj b q) ∧
      (∃ u, IsLeftStar G A C B u ∧ (∃ f ∈ F, G.Adj u f) ∧ ∀ q ∈ Q, G.Adj u q) ∧
      (∀ q ∈ Q, ∃ f ∈ F, G.Adj q f) ∧
      (∀ q ∈ Q, ∃ s ∈ A ∪ B ∪ C, G.Adj q s) ∧
      (∀ q ∈ Q, ¬ IsLeftStar G A C B q) := by sorry

end StrongPerfectGraph.OddPrism
