-- Prove2me | Theorems.Thm_StrongPerfectGraph_OddPrism_maximal_staircase_vertex_types
-- name    : StrongPerfectGraph.OddPrism.maximal_staircase_vertex_types
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:52:57.69444+00:00
-- url     : https://prove2.me/theorems/8a2e3ebc-b128-4003-b378-8a91cefb54bd
-- title:
--   12.1, p. 134 — the vertices outside a maximal staircase are of exactly one of three types
-- statement:
--   Let $G$ be a Berge graph with no appearance of $K_4$, no even prism and no 1-breaker. Let $K=(S=(A,C,B),a_0\text{-}R_0\text{-}b_0)$ be a maximal staircase in $G$ and let $v\in V(G)\setminus V(K)$. Then exactly one of the following holds:
--
--   1. $v$ is minor; and in that case, either $v$ is a left-star or $v$ is not $A$-complete, and either $v$ is a right-star or $v$ is not $B$-complete;
--   2. $v$ is major; and in that case it is left-diagonal, right-diagonal or central;
--   3. $v$ is a left-star with a neighbour in $R_0\setminus a_0$, or a right-star with a neighbour in $R_0\setminus b_0$.
--
--   This classification is the basis for the decomposition in the proof of 13.4.
--
--   **Formalization Note** "Exactly one" is stated for the three headline conditions (minor; major; the star condition of item 3), with the "in that case" clauses as separate implications.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 134, 12.1

import Mathlib
import Definitions.Def_StrongPerfectGraph_OddPrism_IsBerge
import Definitions.Def_StrongPerfectGraph_OddPrism_AppearsIn
import Definitions.Def_StrongPerfectGraph_OddPrism_IsPrism
import Definitions.Def_StrongPerfectGraph_OddPrism_IsStaircase
import Definitions.Def_StrongPerfectGraph_OddPrism_StaircaseVertexTypes
import Definitions.Def_StrongPerfectGraph_OddPrism_IsOneBreaker

namespace StrongPerfectGraph.OddPrism

/-- **12.1** (p. 134). Let `G` be a Berge graph with no appearance of `K₄`, no even prism and
no 1-breaker, let `K = (S = (A, C, B), a₀-R₀-b₀)` be a maximal staircase in `G`, and let
`v ∈ V(G) \ V(K)`. Then exactly one of the following holds:
1. `v` is minor;
2. `v` is major;
3. `v` is a left-star with a neighbour in `R₀ \ a₀`, or a right-star with a neighbour in
   `R₀ \ b₀`.
Moreover, if `v` is minor then either `v` is a left-star or `v` is not `A`-complete, and
either `v` is a right-star or `v` is not `B`-complete; and if `v` is major then it is
left-diagonal, right-diagonal or central. -/
theorem maximal_staircase_vertex_types {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsBerge G) (hK4 : ¬ AppearsIn K4 G)
    (hprism : ¬ ContainsEvenPrism G) (h1 : ¬ HasOneBreaker G)
    (A C B : Set V) (r : List V) (a₀ b₀ : V)
    (hK : IsMaximalStaircase G A C B r)
    (ha₀ : r.head? = some a₀) (hb₀ : r.getLast? = some b₀)
    (v : V) (hvS : v ∉ A ∪ B ∪ C) (hvR : v ∉ r) :
    let minor := IsMinor G A C B r a₀ b₀ v
    let major := IsMajor G A C B r v
    let star := (IsLeftStar G A C B v ∧ ∃ x ∈ r, x ≠ a₀ ∧ G.Adj v x) ∨
      (IsRightStar G A C B v ∧ ∃ x ∈ r, x ≠ b₀ ∧ G.Adj v x)
    ((minor ∧ ¬ major ∧ ¬ star) ∨ (¬ minor ∧ major ∧ ¬ star) ∨
        (¬ minor ∧ ¬ major ∧ star)) ∧
      (minor →
        (IsLeftStar G A C B v ∨ ¬ ∀ a ∈ A, G.Adj v a) ∧
        (IsRightStar G A C B v ∨ ¬ ∀ b ∈ B, G.Adj v b)) ∧
      (major →
        IsLeftDiagonal G A C B r b₀ v ∨ IsRightDiagonal G A C B r a₀ v ∨
          IsCentral G A C B r a₀ b₀ v) := by sorry

end StrongPerfectGraph.OddPrism
