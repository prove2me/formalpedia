-- Prove2me | Theorems.Thm_TreewidthApprox_Pushed_packing_argument
-- name    : TreewidthApprox.Pushed.packing_argument
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:18.466706+00:00
-- url     : https://prove2.me/theorems/657a04ab-ae3c-48f0-b3ed-69868df54aec
-- title:
--   Proof sketch of Lemma 2.2, pp. 321–322 — components with ≤ ½|S| of S each can be split into two sides with ≤ ⅔|S| of S each
-- statement:
--   This is the packing step in the proof sketch of Lemma 2.2.
--
--   Let $G$ be a finite graph and $S, X' \subseteq V(G)$. Suppose every connected component $C$ of $G \setminus X'$ satisfies $|C \cap S| \le \tfrac12 |S|$. Then the components of $G \setminus X'$ can be distributed between a left side and a right side so that each side holds at most two thirds of $S$: there are disjoint sets $L', R'$ with $L' \cup R' = V(G) \setminus X'$, no edge of $G$ between $L'$ and $R'$, and
--
--   $$
--   |L' \cap S| \le \tfrac23 |S|, \qquad |R' \cap S| \le \tfrac23 |S|.
--   $$
--
--   Combined with Lemma 2.1 this gives, for every graph of treewidth at most $k$, a set of at most $k+1$ vertices whose removal splits $S$ into two sides of at most $\tfrac23|S|$ each; with $S = V(G)$ it is the folklore $\tfrac23$-balanced separation used in Lemma 6.5.
--
--   **Formalization Note** "Assigning each component to the left or the right" is encoded as a partition $(L', R')$ of $V(G) \setminus X'$ with no edge between $L'$ and $R'$: such a partition is exactly a union of components on each side. No treewidth hypothesis is needed and none is assumed. The bounds are stated without division as $3\,|L' \cap S| \le 2\,|S|$ and $3\,|R' \cap S| \le 2\,|S|$.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), pp. 321–322, proof sketch of Lemma 2.2, first two sentences

import Mathlib
import Definitions.Def_TreewidthApprox_Pushed_Setting

namespace TreewidthApprox.Pushed

theorem packing_argument {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S X' : Finset V)
    (hX' : ∀ u : V, u ∉ X' → 2 * (avoidComp G X' u ∩ S).card ≤ S.card) :
    ∃ Lft Rgt : Finset V, Disjoint Lft Rgt ∧ Lft ∪ Rgt = Finset.univ \ X' ∧
      NoEdge G Lft Rgt ∧
      3 * (Lft ∩ S).card ≤ 2 * S.card ∧ 3 * (Rgt ∩ S).card ≤ 2 * S.card := by sorry

end TreewidthApprox.Pushed
