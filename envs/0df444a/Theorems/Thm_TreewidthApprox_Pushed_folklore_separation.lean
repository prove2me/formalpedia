-- Prove2me | Theorems.Thm_TreewidthApprox_Pushed_folklore_separation
-- name    : TreewidthApprox.Pushed.folklore_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:27.832568+00:00
-- url     : https://prove2.me/theorems/dfd9680d-c962-4f5c-a748-656162cb64c0
-- title:
--   p. 369 (§6.4.3) — every graph of treewidth ≤ k has a ⅔-balanced separation of order ≤ k+1
-- statement:
--   Let $G$ be a finite graph of treewidth at most $k$. Then $G$ has a $\tfrac23$-balanced separation of order at most $k+1$: a partition $(L, X, R)$ of $V(G)$ with no edge between $L$ and $R$ such that
--
--   $$
--   |X| \le k+1, \qquad |L| \le \tfrac23 |V(G)|, \qquad |R| \le \tfrac23 |V(G)|.
--   $$
--
--   The paper calls this folklore and refers to the proof of Lemma 2.2: it is Lemma 2.1 together with the packing argument, applied with $S = V(G)$. It is the first step of the proof of Lemma 6.5, which intersects this separation with a given $\tfrac34$-balanced one.
--
--   **Formalization Note** Treewidth at most $k$ is `RobertsonSeymour1986.GM5.TreewidthLE G k`. The bounds on $|L|$ and $|R|$ are stated over the reals.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), p. 369, §6.4.3, paragraph before Definition 6.4

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Definitions.Def_TreewidthApprox_Pushed_Setting

namespace TreewidthApprox.Pushed

theorem folklore_separation {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k : ℕ) (htw : RobertsonSeymour1986.GM5.TreewidthLE G k) :
    ∃ L X R : Finset V, IsSeparation G L X R ∧ X.card ≤ k + 1 ∧
      (L.card : ℝ) ≤ 2 / 3 * Fintype.card V ∧ (R.card : ℝ) ≤ 2 / 3 * Fintype.card V := by sorry

end TreewidthApprox.Pushed
