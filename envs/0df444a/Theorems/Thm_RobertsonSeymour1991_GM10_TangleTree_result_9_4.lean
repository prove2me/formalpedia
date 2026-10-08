-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_TangleTree_result_9_4
-- name    : RobertsonSeymour1991.GM10.TangleTree.result_9_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:03.580225+00:00
-- url     : https://prove2.me/theorems/e9cdf5dc-2231-4c08-a1dd-70cb7c60a440
-- title:
--   (9.4), p. 180 — doubly λ-robust separations do not cross
-- statement:
--   Let $\lambda$ be a tie-breaker in a finite hypergraph $G$, and let $(A,B)$, $(C,D)$ be doubly $\lambda$-robust separations of $G$. Then
--   $$(A,B)\ \text{and}\ (C,D)\ \text{do not cross}.$$
--
--   Consequently every set of doubly $\lambda$-robust separations is laminar, which together with (9.1) produces tree-decompositions from such separations.
--
--   **Formalization Note** The tie-breaker $\lambda$ is an explicit hypothesis: the paper's sentence presupposes the $\lambda$ fixed before it.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 180, (9.4)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_TieBreaker
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_Laminar

namespace RobertsonSeymour1991.GM10.TangleTree

/-- (9.4), p. 180. Let `λ` be a tie-breaker in `G`, and let `(A, B)`, `(C, D)` be doubly
`λ`-robust separations of `G`. Then `(A, B)` and `(C, D)` do not cross. -/
theorem result_9_4 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E)
    {Λ : Type} [LinearOrder Λ] (lam : G.Sub × G.Sub → Λ) (hlam : G.IsTieBreaker lam)
    (A B C D : G.Sub) (hAB : Hypergraph.IsSeparation A B) (hCD : Hypergraph.IsSeparation C D)
    (hrAB : Hypergraph.IsDoublyRobust lam A B) (hrCD : Hypergraph.IsDoublyRobust lam C D) :
    ¬ Hypergraph.Crosses (A, B) (C, D) := by sorry

end RobertsonSeymour1991.GM10.TangleTree
