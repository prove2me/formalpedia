-- Prove2me | Theorems.Thm_SingleMachinePrec_Framework_prop_3_2
-- name    : SingleMachinePrec.Framework.prop_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:29:08.426738+00:00
-- url     : https://prove2.me/theorems/8ab022c5-26f0-4b92-8357-c775b91323b6
-- title:
--   Proposition 3.2 — the vertex cover graph G^S_P equals the graph of incomparable pairs G_P
-- statement:
--   Let $P$ be a partial order on a finite set $N$ of jobs. Let $G^S_P$ be the vertex cover graph of Correa and Schulz (nodes: the incomparable pairs; adjacency: the symmetric closure of the three-case rule of §2.2) and $G_P$ the graph of incomparable pairs of dimension theory (nodes: the incomparable pairs; edges: the 2-element sets of incomparable pairs that are minimal among the sets no linear extension of $P$ reverses entirely). Then
--   $$G^S_P = G_P.$$
--
--   The proposition identifies the scheduling-side graph, defined through the constraints of an integer program, with a graph defined purely through the linear extensions of $P$. It is what lets colorings and fractional colorings coming from realizers of $P$ be used for vertex cover in $G^S_P$.
--
--   **Formalization Note** The two graphs are stated equal as `SimpleGraph`s on the common vertex type of incomparable pairs. The paper introduces $G_P$ for a poset that is not a linear order; the statement is made for every partial order (for a linear order both graphs have no vertices).
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 657, Proposition 3.2

import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_VertexCoverGraph

namespace SingleMachinePrec.Framework

/-- **Proposition 3.2** (p. 657). For every finite poset `P`, the vertex cover graph `G^S_P` of
`1|prec|∑ w_j C_j` and the graph of incomparable pairs `G_P` coincide. -/
theorem prop_3_2 {N : Type*} [Fintype N] (P : N → N → Prop) [IsPartialOrder N P] :
    vertexCoverGraph P = incPairsGraph P := by sorry

end SingleMachinePrec.Framework
