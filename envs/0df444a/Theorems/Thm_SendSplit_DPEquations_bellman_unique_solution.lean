-- Prove2me | Theorems.Thm_SendSplit_DPEquations_bellman_unique_solution
-- name    : SendSplit.DPEquations.bellman_unique_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:13:40.484767+00:00
-- url     : https://prove2.me/theorems/3439b5c4-cb53-464c-b270-052912a5e846
-- title:
--   Eq. (2)′ — with positive circuits, Bellman's equations have a unique +∞-or-real solution
-- statement:
--   Let $G$ be a finite directed graph without loops, with real arc costs $a_{kj}$ on its arcs and a destination node $t$ from which no arc leaves. Suppose that **every simple circuit of $G$ has positive cost**. Then every $+\infty$ or real-valued solution $C$ of Bellman's equations
--
--   $$C_t = 0, \qquad C_k = \min_{(k,j)} \bigl[ a_{kj} + C_j \bigr] \quad (k \neq t)$$
--
--   equals the vector of minimum chain costs: $C_k = \bar C_k = \inf \{ \text{cost of } P : P \text{ a chain from } k \text{ to } t \}$ for every node $k$ (with $+\infty$ when no chain exists).
--
--   In the proof of Theorem 2 this gives uniqueness of the solution of (2)′ for each fixed $I$, and hence, by induction on $|I|$, uniqueness in Theorem 2.
--
--   **Formalization Note** Same encoding as the preceding milestone: missing arcs are cost $+\infty$, chains are walks.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 642, Section 3, proof of Theorem 2

import Mathlib
import Definitions.Def_BertsekasSPGraph
import Definitions.Def_SendSplit_DPEquations_Bellman

namespace SendSplit.DPEquations

theorem bellman_unique_solution {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasSPGraph V)
    (hloop : ∀ i, (i, i) ∉ G.arcs) (hout : ∀ j, (G.t, j) ∉ G.arcs)
    (hpos : ∀ l, IsSimpleCircuit G l → 0 < circuitLength G l) :
    ∀ C : V → EReal, IsBellmanSolution G C → ∀ k, C k = BertsekasShortestDistance G k G.t := by sorry

end SendSplit.DPEquations
