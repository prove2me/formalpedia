-- Prove2me | Theorems.Thm_SingleMachinePrec_IntervalReduction_claim_1
-- name    : SingleMachinePrec.IntervalReduction.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:08:04.965609+00:00
-- url     : https://prove2.me/theorems/0da41db8-f559-4465-831d-03beba7ff0b5
-- title:
--   Claim 1 — $\tau(G') = \tau(G) + |V| + |E\setminus E_T|$
-- statement:
--   Let $G=(V,E)$ be a graph with a tree layout $T=(V,E_T)$, and let $G'$ be the gadget graph of Stage 1. Write $\tau(H)$ for the minimum size of a vertex cover of a graph $H$. Then
--   $$\tau(G') = \tau(G) + |V| + |E\setminus E_T|.$$
--
--   In the paper's words: if $C_*\subseteq V$ and $C'_*\subseteq V'$ are optimum vertex covers of $G$ and $G'$, then $|C_*| = |C'_*| - |V| - |E\setminus E_T|$. The construction follows Alimonti and Kann's proof of APX-completeness of vertex cover on cubic graphs. It transfers the vertex cover problem on $G$ to the graph $G'$, which the scheduling instance reproduces.
--
--   **Formalization Note** $\tau$ is Mathlib's `SimpleGraph.vertexCoverNum`, valued in $\mathbb N\cup\{\infty\}$ (finite here). The claim does not use connectivity of $G$ or the degree bound, and holds for any parent-first spanning tree.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 662, Claim 1

import Mathlib
import Definitions.Def_SingleMachinePrec_IntervalReduction_TreeLayout

namespace SingleMachinePrec.IntervalReduction

/-- Claim 1 (p. 662): the minimum vertex cover of `G′` is larger than that of `G` by exactly
`|V| + |E \ E_T|`. -/
theorem claim_1 {N : ℕ} (G : SimpleGraph (Fin N)) (L : TreeLayout G) :
    (GPrime L).vertexCoverNum =
      G.vertexCoverNum + (N : ℕ∞) + (Fintype.card (NonTreeEdge L) : ℕ∞) := by sorry

end SingleMachinePrec.IntervalReduction
