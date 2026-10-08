-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_TangleTree_result_9_1
-- name    : RobertsonSeymour1991.GM10.TangleTree.result_9_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:46.232789+00:00
-- url     : https://prove2.me/theorems/70b5ad6f-ca99-4e58-a833-f46c8e04c0a2
-- title:
--   (9.1), p. 177 — separations made by a tree-decomposition are laminar, and every laminar set is so realised
-- statement:
--   Let $G$ be a finite hypergraph.
--
--   1. If $(T,\tau)$ is a tree-decomposition of $G$, then the set of all separations of $G$ made by edges of $T$ is laminar.
--   2. Conversely, if $\{(A_i,B_i):1\le i\le k\}$ is a laminar set of separations of $G$, there is a tree-decomposition $(T,\tau)$ of $G$ such that
--      - for $1\le i\le k$, $(A_i,B_i)$ is made by a unique edge of $T$, and
--      - for each edge $e$ of $T$, at least one of the two separations made by $e$ equals $(A_i,B_i)$ for some $i$.
--
--   In short,
--   $$\{\text{laminar sets of separations of } G\}\ \longleftrightarrow\ \{\text{edge-separation systems of tree-decompositions of } G\}.$$
--   This is the bridge from "pairwise non-crossing" to "tree-shaped", used in (10.3) to turn the distinctions between tangles into a tree-decomposition.
--
--   **Formalization Note** "Made by a unique edge" is $\exists!$ over unordered edges `e : Sym2 (Fin n)` of $T$ with `Makes D e p` (either orientation). The finite index set $\{1,\dots,k\}$ is replaced by an arbitrary set `S` of separations, which is finite because $G$ is. The paper leaves the proof to the reader.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 177, (9.1)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_TreeDecomposition
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_Laminar

namespace RobertsonSeymour1991.GM10.TangleTree

/-- (9.1), p. 177. If `(T, τ)` is a tree-decomposition of `G`, then the set of all separations
made by edges of `T` is laminar. Conversely, for every laminar set `S` of separations of `G`
there is a tree-decomposition `(T, τ)` such that (i) every member of `S` is made by a unique edge
of `T`, and (ii) for each edge of `T`, at least one of the two separations it makes is in `S`. -/
theorem result_9_1 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) :
    (∀ (n : ℕ) (D : TreeDecomposition G n),
      Hypergraph.IsLaminar {p | ∃ u w, D.T.Adj u w ∧ D.madeBy u w = p}) ∧
    (∀ S : Set (G.Sub × G.Sub), (∀ p ∈ S, Hypergraph.IsSeparation p.1 p.2) →
      Hypergraph.IsLaminar S →
      ∃ (n : ℕ) (D : TreeDecomposition G n),
        (∀ p ∈ S, ∃! e : Sym2 (Fin n), D.Makes e p) ∧
        (∀ u w, D.T.Adj u w → D.madeBy u w ∈ S ∨ D.madeBy w u ∈ S)) := by sorry

end RobertsonSeymour1991.GM10.TangleTree
