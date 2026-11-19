-- Prove2me | Theorems.Thm_TenChallenges_bounded_treewidth_wqo
-- name    : TenChallenges.bounded_treewidth_wqo
-- status  : Open
-- author  : @Davide
-- created : 2026-11-18T12:23:42.782519+00:00
-- url     : https://prove2.me/theorems/2d88a89b-7dbe-489f-96ab-2c92bc9803c5
-- title:
--   Graph Minors IV: graphs of bounded tree-width are well-quasi-ordered by minors
-- statement:
--   **Graphs of bounded tree-width are well-quasi-ordered by minors.** Fix an integer $w\ge 0$. For every infinite sequence $G_0,G_1,G_2,\dots$ of finite simple graphs, each of tree-width at most $w$, there are indices $i<j$ such that $G_i$ is a minor of $G_j$:
--
--   $$\forall n:\ \operatorname{tw}(G_n)\le w\quad\Longrightarrow\quad \exists\, i<j:\ G_i\preceq G_j.$$
--
--   This is the main theorem of Graph Minors IV, proved by Robertson and Seymour with a Nash-Williams-style minimal bad sequence argument on tree-decompositions. Combined with the Excluded Grid Theorem of Graph Minors V, it gives that every class excluding a fixed planar minor is well-quasi-ordered, and in particular that finite planar graphs are.
--
--   **Formalization Note** Tree-width at most $w$ is `TreewidthLE G w` from Graph Minors V (a tree-decomposition with bags of size at most $w+1$); so the hypothesis is tree-width $< w+1$, matching the paper's "tree-width $< k$" with $k=w+1$. Graphs are `FiniteGraph` (simple graphs on `Fin n`), and the minor relation is the branch-set model `FiniteGraph.MinorLE`.
-- source:
--   N. Robertson, P. D. Seymour, Graph Minors. IV. Tree-width and well-quasi-ordering, J. Combin. Theory Ser. B 48 (1990), 227–254, statement (1.5): 'For any integer k the class of all graphs with tree-width < k is well-quasi-ordered by minors.' https://web.math.princeton.edu/~pds/papers/GM4/paper.pdf

import Definitions.Def_TenChallenges_AlphaWQO
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

namespace TenChallenges
theorem bounded_treewidth_wqo (w : ℕ) (f : ℕ → FiniteGraph)
    (hf : ∀ n, RobertsonSeymour1986.GM5.TreewidthLE (f n).2 w) :
    ∃ i j, i < j ∧ FiniteGraph.MinorLE (f i) (f j) := by sorry
end TenChallenges
