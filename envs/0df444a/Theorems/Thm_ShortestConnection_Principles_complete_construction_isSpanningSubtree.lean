-- Prove2me | Theorems.Thm_ShortestConnection_Principles_complete_construction_isSpanningSubtree
-- name    : ShortestConnection.Principles.complete_construction_isSpanningSubtree
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:55:08.565274+00:00
-- url     : https://prove2.me/theorems/d5b674ee-e8e8-4cba-8995-bcdbc9458e95
-- title:
--   §II — a complete construction (N − 1 applications) is a spanning subtree
-- statement:
--   Let $G$ be a connected simple graph on a finite set $V$ of $N$ terminals with real edge lengths $w$. If $e_0,\dots,e_{N-2}$ is a complete construction by P1 and P2 (exactly $N-1$ applications), then its links form a spanning subtree of $G$:
--   $$\{e_0,\dots,e_{N-2}\} \subseteq E(G) \quad\text{and}\quad H(\{e_0,\dots,e_{N-2}\}) \text{ is a tree on } V.$$
--
--   This is Prim's "an $N$-terminal network is connected by $N-1$ applications": the output of a complete construction is a connection network.
--
--   **Formalization Note** The connectivity of $G$ is an implicit hypothesis of the paper, stated explicitly here; it guarantees $V \ne \emptyset$, so $N-1$ is ordinary subtraction.
-- source:
--   Prim, Shortest Connection Networks And Some Generalizations, Bell System Tech. J. 36 (1957), p. 1392, §II

import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

/-- Prim 1957, §II, p. 1392 ("an N-terminal network is connected by N-1 applications"): the
links of a complete construction by P1 and P2 (one with `N - 1` links, `N = card V`) form a
spanning subtree of the labelled graph `G`.
Implicit hypothesis made explicit: `G` is connected (in particular `V` is nonempty, so
`card V - 1` is ordinary subtraction). -/
theorem complete_construction_isSpanningSubtree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (w : Sym2 V → ℝ) (l : List (Sym2 V))
    (hl : IsCompleteConstruction G w l) :
    IsSpanningSubtree G l.toFinset := by sorry

end ShortestConnection.Principles
