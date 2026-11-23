-- Prove2me | Theorems.Thm_TenChallenges_bounded_treewidth_sets_wqo
-- name    : TenChallenges.bounded_treewidth_sets_wqo
-- status  : Open
-- author  : @Davide
-- created : 2026-11-23T11:42:36.332713+00:00
-- url     : https://prove2.me/theorems/a1af5a40-c0be-4c54-8ef8-77aa521ac306
-- title:
--   Sets of finite graphs of bounded tree-width are well-quasi-ordered under minors
-- statement:
--   **Sets of graphs of bounded tree-width.** Fix an integer $w\ge 0$ and let $X_0,X_1,\dots$ be sets of finite simple graphs such that every graph in every $X_n$ has tree-width at most $w$. Then there are indices $i<j$ such that every graph in $X_i$ is a minor of some graph in $X_j$:
--
--   $$\exists\, i<j\ \ \forall G\in X_i\ \ \exists H\in X_j:\ G\preceq H.$$
--
--   Thus finite graphs of tree-width at most $w$ are $1$-well-quasi-ordered by the minor relation. For singletons $X_n$ this is the theorem of Graph Minors IV. The general statement is a consequence of Thomas's theorem on infinite graphs with a forbidden finite planar minor, applied to the disjoint unions of infinitely many copies of the graphs in $X_n$, each enlarged by a vertex adjacent to all its vertices.
--
--   **Formalization Note** The sets $X_n$ may be empty or infinite; an empty set lies below every set.
-- source:
--   R. Thomas, Well-quasi-ordering infinite graphs with forbidden finite planar minor, Trans. Amer. Math. Soc. 312 (1989), 279-313, https://www.ams.org/journals/tran/1989-312-01/S0002-9947-1989-0932450-9. Consequence of the main theorem as stated in the abstract (a sequence of possibly infinite graphs whose first member is finite and planar has i<j with G_i a minor of G_j).

import Definitions.Def_TenChallenges_AlphaWQO
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

namespace TenChallenges
theorem bounded_treewidth_sets_wqo (w : ℕ) (X : ℕ → Set FiniteGraph)
    (hX : ∀ n, ∀ G ∈ X n, RobertsonSeymour1986.GM5.TreewidthLE G.2 w) :
    ∃ i j, i < j ∧ ∀ G ∈ X i, ∃ H ∈ X j, FiniteGraph.MinorLE G H := by sorry
end TenChallenges
