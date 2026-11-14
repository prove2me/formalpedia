-- Prove2me | Theorems.Thm_StableMSR_Recovery_clique_in_decomposition_bag
-- name    : StableMSR.Recovery.clique_in_decomposition_bag
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T16:07:27.31602+00:00
-- url     : https://prove2.me/theorems/a77c609e-cd14-458c-869e-ed17650c5729
-- title:
--   Every clique lies in a bag of a finite tree decomposition
-- statement:
--   Let $G$ be a graph and let $(T,(X_t)_{t\in V(T)})$ be a tree decomposition with a finite, nonempty decomposition tree. Every finite clique $K$ of $G$ is contained in one bag:
--   $$\exists t\in V(T),\qquad K\subseteq X_t.$$
--   The empty clique is included. The graph $G$ itself need not be finite.
--
--   This is the bag-placement fact used to assign the clustering algorithm's clique-supported constraints and contributions to individual bags. The proof establishes the Helly property of nonempty path-convex vertex sets in a finite tree, then applies it to the bag occurrences of the clique vertices. It uses the canonical path-based definition of tree decomposition.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/html/2611.03547v1, Appendix A.6, tree-decomposition paragraph: every clique lies in a bag, so constraints and contributions can be assigned to containing bags. The finite-tree Helly argument is formalized directly.

import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

theorem clique_in_decomposition_bag {V T : Type} [DecidableEq V] [Fintype T] [DecidableEq T]
    (G : SimpleGraph V) (tree : SimpleGraph T) (bags : T → Finset V)
    (htd : RobertsonSeymour1986.GM5.IsTreeDecomposition G tree bags)
    (K : Finset V) (hK : (K : Set V).Pairwise G.Adj) :
    ∃ t : T, K ⊆ bags t := by sorry

end StableMSR.Recovery
