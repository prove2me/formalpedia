-- Prove2me | Theorems.Thm_ShortestConnection_Principles_p1_p2_provide_sss
-- name    : ShortestConnection.Principles.p1_p2_provide_sss
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:58:35.504302+00:00
-- url     : https://prove2.me/theorems/d88ef04f-3adf-437a-b630-905eedc397b7
-- title:
--   P1 and P2 provide a shortest spanning subtree for any connected labelled graph with real edge lengths
-- statement:
--   Let $G$ be a connected simple graph on a finite set $V$ of $N$ terminals, and let $w$ assign an arbitrary real length to every edge (lengths may be zero, negative, or of mixed sign, and may tie). Then:
--
--   1. a complete construction by P1 and P2 exists: a sequence of $N-1$ links, each an application of Principle 1 or Principle 2 with respect to the links made before it;
--   2. the links $F$ of every complete construction form a shortest spanning subtree of $G$:
--   $$F \text{ is a spanning subtree of } G \quad\text{and}\quad \sum_{e\in F} w(e) \le \sum_{e\in F'} w(e) \text{ for every spanning subtree } F' \text{ of } G.$$
--
--   This is the general statement of §IV of Prim's paper: "P1 and P2 will provide a SSS for any connected labelled graph with any set of real edge lengths." It contains the Basic Problem (complete graph, Euclidean distances) and the incomplete-graph case, and every choice of isolated terminal or fragment, of order, and of tie-breaking among nearest neighbors.
--
--   **Formalization Note** Missing edges of $G$ are never links (they have infinite length in Prim's distance table). The existence clause is part of "will provide" and rules out a vacuous reading.
-- source:
--   Prim, Shortest Connection Networks And Some Generalizations, Bell System Tech. J. 36 (1957), p. 1396, §IV

import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

/-- Prim 1957, §IV, p. 1396: "P1 and P2 will provide a SSS for any connected labelled graph with
any set of real edge "lengths." The "lengths" need not even be positive, or of the same sign."
For every finite connected graph `G` and every real edge lengths `w`, a complete construction by
P1 and P2 (`N - 1` applications, `N = card V`) exists, and the links of every complete
construction form a shortest spanning subtree of `G`. -/
theorem p1_p2_provide_sss {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (w : Sym2 V → ℝ) :
    (∃ l : List (Sym2 V), IsCompleteConstruction G w l) ∧
      ∀ l : List (Sym2 V), IsCompleteConstruction G w l → IsSSS G w l.toFinset := by sorry

end ShortestConnection.Principles
