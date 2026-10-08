-- Prove2me | Theorems.Thm_TreewidthApprox_Pushed_lemma_2_1
-- name    : TreewidthApprox.Pushed.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:35.062157+00:00
-- url     : https://prove2.me/theorems/5ecfc625-bacb-44a6-943c-0e2a388c2dd7
-- title:
--   Lemma 2.1 (Graph Minors II) — if tw(G) ≤ k, some X with |X| ≤ k+1 leaves every component of G ∖ X with ≤ ½|S| vertices of S
-- statement:
--   This is the balanced-separator lemma of Robertson and Seymour (Graph Minors II), as stated and used by Bodlaender et al.
--
--   Let $G$ be a finite graph of treewidth at most $k$, and let $S \subseteq V(G)$. Then there is a set $X \subseteq V(G)$ with $|X| \le k+1$ such that every connected component $C$ of $G \setminus X$ contains at most half of the vertices of $S$:
--
--   $$
--   |C \cap S| \le \tfrac{1}{2}|S| \quad \text{for every component } C \text{ of } G \setminus X.
--   $$
--
--   Such an $X$ is called a balanced $S$-separator. The paper deliberately uses this form, with $\tfrac12|S|$, rather than Graph Minors II's slightly stronger bound $\tfrac12|S \setminus X|$. Taking $S = V(G)$ gives the familiar fact that graphs of treewidth $k$ have balanced separators of size $k+1$.
--
--   **Formalization Note** "Treewidth at most $k$" is the published definition `RobertsonSeymour1986.GM5.TreewidthLE G k` (a tree decomposition whose bags have at most $k+1$ vertices); Definition 1.1 of the paper roots the decomposition tree, which does not change the width. The component of $G \setminus X$ containing $u \notin X$ is `avoidComp G X u` (vertices joined to $u$ by a walk avoiding $X$). The bound is stated without division as $2\,|C \cap S| \le |S|$.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), p. 321, Lemma 2.1 (citing Robertson and Seymour, Graph Minors II, J. Algorithms 7 (1986))

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Definitions.Def_TreewidthApprox_Pushed_Setting

namespace TreewidthApprox.Pushed

theorem lemma_2_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ)
    (htw : RobertsonSeymour1986.GM5.TreewidthLE G k) (S : Finset V) :
    ∃ X : Finset V, X.card ≤ k + 1 ∧
      ∀ u : V, u ∉ X → 2 * (avoidComp G X u ∩ S).card ≤ S.card := by sorry

end TreewidthApprox.Pushed
