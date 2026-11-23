-- Prove2me | Theorems.Thm_TenChallenges_planar_sets_increasing_treewidth_wqo
-- name    : TenChallenges.planar_sets_increasing_treewidth_wqo
-- status  : Open
-- author  : @Davide
-- created : 2026-11-23T11:42:36.993856+00:00
-- url     : https://prove2.me/theorems/818415f0-5577-4f56-adfb-45ac0269ab43
-- title:
--   Sets of planar graphs of strictly increasing bounded tree-width are well-quasi-ordered under minors
-- statement:
--   **Sets of planar graphs of strictly increasing tree-width.** Let $w_0<w_1<w_2<\cdots$ be integers and let $X_0,X_1,\dots$ be sets of finite planar graphs such that, for every $n$,
--
--   1. every graph in $X_n$ has tree-width at most $w_n$;
--   2. some graph in $X_{n+1}$ has tree-width greater than $w_n$.
--
--   Then there are indices $i<j$ such that every graph in $X_i$ is a minor of some graph in $X_j$:
--
--   $$\exists\, i<j\ \ \forall G\in X_i\ \ \exists H\in X_j:\ G\preceq H.$$
--
--   This is the part of the rung $r=2$ that is not covered by known results on graphs of bounded tree-width. No proof is known to the submitter: it is a special case of an open question, stated as a conjecture.
--
--   **Formalization Note** The sets $X_n$ may be infinite, and planarity is Wagner's criterion, as in the mission.
-- source:
--   Special case of rung r = 2 of the Ten Challenges 06 mission (TenChallenges.challenge_06_r2); compare Georgakopoulos 2025, https://arxiv.org/abs/2510.19285, Problem 1.3, which asks the question for sets of arbitrary finite graphs.

import Mathlib.Order.Monotone.Defs
import Definitions.Def_TenChallenges_AlphaWQO
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

namespace TenChallenges
theorem planar_sets_increasing_treewidth_wqo (w : ℕ → ℕ) (hw : StrictMono w)
    (X : ℕ → Set PlanarGraph)
    (hX : ∀ n, ∀ G ∈ X n, RobertsonSeymour1986.GM5.TreewidthLE G.val.2 (w n))
    (hX' : ∀ n, ∃ G ∈ X (n + 1), ¬ RobertsonSeymour1986.GM5.TreewidthLE G.val.2 (w n)) :
    ∃ i j, i < j ∧ ∀ G ∈ X i, ∃ H ∈ X j, PlanarGraph.MinorLE G H := by sorry
end TenChallenges
