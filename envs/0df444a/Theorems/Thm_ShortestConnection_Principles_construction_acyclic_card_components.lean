-- Prove2me | Theorems.Thm_ShortestConnection_Principles_construction_acyclic_card_components
-- name    : ShortestConnection.Principles.construction_acyclic_card_components
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:54:31.652284+00:00
-- url     : https://prove2.me/theorems/ea77e897-e838-4911-8021-de1d651203ca
-- title:
--   §II — each application of P1 or P2 joins two components: no loops, N − k components
-- statement:
--   Let $G$ be a simple graph on a finite set $V$ of $N$ terminals with real edge lengths $w$, and let $e_0,\dots,e_{k-1}$ be a construction by P1 and P2. Then the links $F = \{e_0,\dots,e_{k-1}\}$ contain no closed loop, and the number of connected components of the link graph $H(F)$ (isolated terminals and isolated fragments together) is
--   $$\#\,\mathrm{components}\bigl(H(F)\bigr) = N - k.$$
--
--   This is Prim's observation that each application of either principle reduces the number of isolated terminals and fragments by one; it is the counting step behind "an $N$-terminal network is connected by $N-1$ applications".
--
--   **Formalization Note** The component count is `Nat.card` of the connected components of the link graph; $N - k$ is natural-number subtraction. No connectivity of $G$ is needed.
-- source:
--   Prim, Shortest Connection Networks And Some Generalizations, Bell System Tech. J. 36 (1957), p. 1392, §II

import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

/-- Prim 1957, §II, p. 1392 ("each application of either P1 or P2 reduces the total number of
isolated terminals and fragments by one"): after the links of any construction by P1 and P2 have
been made, the links form no closed loop, and the number of connected components (isolated
terminals and isolated fragments) is the number of terminals minus the number of links made.
No hypothesis on `G` or on the lengths is needed. -/
theorem construction_acyclic_card_components {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (l : List (Sym2 V)) (hl : IsConstruction G w l) :
    (linkGraph l.toFinset).IsAcyclic ∧
      Nat.card (linkGraph l.toFinset).ConnectedComponent = Fintype.card V - l.length := by sorry

end ShortestConnection.Principles
