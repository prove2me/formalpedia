-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_TangleTree_result_9_3
-- name    : RobertsonSeymour1991.GM10.TangleTree.result_9_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:43.439654+00:00
-- url     : https://prove2.me/theorems/c146efdf-b28b-4429-aa8a-33f642b72d7f
-- title:
--   (9.3), p. 179 — strengthened second tie-breaker axiom
-- statement:
--   Let $\lambda$ be a tie-breaker in a finite hypergraph $G$, and let $(A,B)$, $(C,D)$ be separations of $G$. Then at least one of the following holds:
--
--   1. $\lambda(A\cup C,\,B\cap D)<\lambda(A,B)$;
--   2. $\lambda(A\cap C,\,B\cup D)<\lambda(C,D)$;
--   3. $C\subseteq A$ and $B\subseteq D$;
--   4. $B=C=G$, $A=D$ and $E(A)=\emptyset$.
--
--   This sharpens the second tie-breaker axiom by replacing "at most" with "smaller than", at the cost of the two degenerate alternatives; it is the tool behind (9.4).
--
--   **Formalization Note** $G$ as a subhypergraph of itself is `Sub.top G`; $\subseteq$ is `Sub.le` (inclusion of both vertex and edge sets).
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 179, (9.3)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_TieBreaker

namespace RobertsonSeymour1991.GM10.TangleTree

/-- (9.3), p. 179. Let `λ` be a tie-breaker in `G` and `(A, B)`, `(C, D)` separations of `G`.
Then (i) `(A ∪ C, B ∩ D)` has smaller `λ`-order than `(A, B)`, or (ii) `(A ∩ C, B ∪ D)` has
smaller `λ`-order than `(C, D)`, or (iii) `C ⊆ A` and `B ⊆ D`, or
(iv) `B = C = G`, `A = D` and `E(A) = ∅`. -/
theorem result_9_3 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E)
    {Λ : Type} [LinearOrder Λ] (lam : G.Sub × G.Sub → Λ) (hlam : G.IsTieBreaker lam)
    (A B C D : G.Sub) (hAB : Hypergraph.IsSeparation A B) (hCD : Hypergraph.IsSeparation C D) :
    lam (A.union C, B.inter D) < lam (A, B) ∨
    lam (A.inter C, B.union D) < lam (C, D) ∨
    (C.le A ∧ B.le D) ∨
    (B = Hypergraph.Sub.top G ∧ C = Hypergraph.Sub.top G ∧ A = D ∧ A.edges = ∅) := by sorry

end RobertsonSeymour1991.GM10.TangleTree
