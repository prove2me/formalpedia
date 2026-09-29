-- Prove2me | Theorems.Thm_ShortestConnection_Principles_construction_extends
-- name    : ShortestConnection.Principles.construction_extends
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:55:50.935836+00:00
-- url     : https://prove2.me/theorems/0616d955-f771-48a1-8542-0da71c12ae99
-- title:
--   §II — a construction with fewer than N − 1 links can be extended by P1 or P2
-- statement:
--   Let $G$ be a connected simple graph on a finite set $V$ of $N$ terminals with real edge lengths $w$, and let $e_0,\dots,e_{k-1}$ be a construction by P1 and P2 with
--   $$k < N - 1.$$
--   Then there is a link $e$ such that $e_0,\dots,e_{k-1},e$ is again a construction by P1 and P2.
--
--   This makes explicit the "can be connected" of the two principles: as long as the network is not yet connected, some isolated terminal or isolated fragment admits an application of P1 or P2. Together with the preceding milestones it shows that complete constructions exist.
--
--   **Formalization Note** The connectivity of $G$ is an implicit hypothesis of the paper, stated explicitly here. In an incomplete graph only edges of $G$ are possible links.
-- source:
--   Prim, Shortest Connection Networks And Some Generalizations, Bell System Tech. J. 36 (1957), pp. 1391-1392, §II (Principle 1, Principle 2; N-1 applications)

import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

/-- Prim 1957, §II, pp. 1391–1392 (P1 and P2: an isolated terminal or fragment "can be
connected"; "an N-terminal network is connected by N-1 applications"): in a connected labelled
graph, a construction by P1 and P2 with fewer than `N - 1` links can always be extended by one
more application of P1 or P2. This is the "can be connected" of the principles made explicit.
Implicit hypothesis made explicit: `G` is connected. -/
theorem construction_extends {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (w : Sym2 V → ℝ) (l : List (Sym2 V))
    (hl : IsConstruction G w l) (hlen : l.length < Fintype.card V - 1) :
    ∃ e : Sym2 V, IsConstruction G w (l ++ [e]) := by sorry

end ShortestConnection.Principles
