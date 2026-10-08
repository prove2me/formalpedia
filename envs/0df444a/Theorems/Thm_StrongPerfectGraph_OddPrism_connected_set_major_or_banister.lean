-- Prove2me | Theorems.Thm_StrongPerfectGraph_OddPrism_connected_set_major_or_banister
-- name    : StrongPerfectGraph.OddPrism.connected_set_major_or_banister
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:52:58.661998+00:00
-- url     : https://prove2.me/theorems/9a25116d-d05d-41fd-b534-b06ae79654a0
-- title:
--   12.3, p. 138 — a connected set with a left-star and an attachment in B ∪ C contains a major vertex or a banister
-- statement:
--   Let $G$ be a Berge graph with no appearance of $K_4$, no even prism and no 1-breaker, and let $K=(S=(A,C,B),a_0\text{-}R_0\text{-}b_0)$ be a maximal staircase in $G$. Let $F\subseteq V(G)\setminus V(S)$ be connected, containing a left-star and with an attachment in $B\cup C$ (a vertex of $B\cup C$ with a neighbour in $F$); $F$ may intersect $V(R_0)$. Then
--   $$F \text{ contains a major vertex or a banister.}$$
--
--   This is used in 13.3 and in the proof of 13.4 to control the components left after deleting a staircase and its stars.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 138, 12.3

import Mathlib
import Definitions.Def_StrongPerfectGraph_OddPrism_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_IsProperTwoJoin
import Definitions.Def_StrongPerfectGraph_OddPrism_AppearsIn
import Definitions.Def_StrongPerfectGraph_OddPrism_IsPrism
import Definitions.Def_StrongPerfectGraph_OddPrism_IsStaircase
import Definitions.Def_StrongPerfectGraph_OddPrism_StaircaseVertexTypes
import Definitions.Def_StrongPerfectGraph_OddPrism_IsOneBreaker

namespace StrongPerfectGraph.OddPrism

/-- **12.3** (p. 138). Let `G` be a Berge graph with no appearance of `K₄`, no even prism and
no 1-breaker, let `K = (S = (A, C, B), a₀-R₀-b₀)` be a maximal staircase in `G`, and let
`F ⊆ V(G) \ V(S)` be connected, containing a left-star and with an attachment in `B ∪ C`
(`F` may intersect `V(R₀)`). Then `F` contains either a major vertex or a banister. -/
theorem connected_set_major_or_banister {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsBerge G) (hK4 : ¬ AppearsIn K4 G)
    (hprism : ¬ ContainsEvenPrism G) (h1 : ¬ HasOneBreaker G)
    (A C B : Set V) (r : List V) (hK : IsMaximalStaircase G A C B r)
    (F : Set V) (hFS : F ⊆ (A ∪ B ∪ C)ᶜ) (hFconn : StrongPerfectGraph.Main.IsConnectedSet G F)
    (hFleft : ∃ u ∈ F, IsLeftStar G A C B u)
    (hFatt : ∃ s ∈ B ∪ C, ∃ f ∈ F, G.Adj s f) :
    (∃ v ∈ F, IsMajor G A C B r v) ∨
      ∃ R : List V, IsBanister G A C B R ∧ ∀ x ∈ R, x ∈ F := by sorry

end StrongPerfectGraph.OddPrism
