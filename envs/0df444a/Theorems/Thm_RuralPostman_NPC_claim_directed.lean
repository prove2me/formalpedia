-- Prove2me | Theorems.Thm_RuralPostman_NPC_claim_directed
-- name    : RuralPostman.NPC.claim_directed
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:02.468235+00:00
-- url     : https://prove2.me/theorems/2163b954-42fc-4d76-b0c2-f3d249fcd709
-- title:
--   §2, p. 6, proof of the Theorem (corrected: |V| ≠ 1) — H has a hamilton circuit iff G has a directed postman's tour of weight ≤ k
-- statement:
--   Let $H$ be a directed graph on $V=\{0,\dots,v-1\}$ with $v\neq 1$, and let $G$ be the rural postman instance of the directed construction: for each vertex $s$ a required arc $(\langle s,0\rangle,\langle s,1\rangle)$ and a non-required arc $(\langle s,1\rangle,\langle s,0\rangle)$, both of weight $0$; an arc $(\langle s,0\rangle,\langle t,0\rangle)$ of weight $1$ for each arc $(s,t)$ of $H$; and $k=v$. Then
--   $$
--   H \text{ has a hamilton circuit} \iff G \text{ has a directed postman's tour of weight} \le k .
--   $$
--
--   The paper states this equivalence without a size condition and leaves the proof to the reader. It fails for $v=1$: the one-vertex graph without arcs has no hamilton circuit, yet $\langle s,0\rangle\to\langle s,1\rangle\to\langle s,0\rangle$ is a directed postman's tour of weight $0\le 1$. For $v\ge 2$ (and trivially for $v=0$) the equivalence holds. The equivalence is what makes the construction a reduction from DIRECTED HAMILTON CIRCUIT to DIRECTED RURAL POSTMAN.
--
--   **Formalization Note** Nodes are 0-based: $V$ is `Fin v`, and $N = V\times\{0,1\}$ is `Fin (v + v)` with $\langle s,0\rangle$ = `Fin.castAdd v s` and $\langle s,1\rangle$ = `Fin.natAdd v s`. A tour is a list of traversals (arc index, direction); `IsRequired e` says that arc $e$ lies in $R$, and `List.countP` counts traversals. $H$ is a Boolean adjacency matrix; a loop $(s,s)$ of $H$ gives an arc $(\langle s,0\rangle,\langle s,0\rangle)$ of weight $1$. For $v=0$ both sides hold: the hamilton-circuit predicate is vacuous on the empty vertex set and the empty tour is a postman's tour of the empty instance.
--
--   Differences from the source:
--   - correction: the equivalence for every directed graph H → hypothesis v ≠ 1; reason: counterexample: H = ({s}, ∅) has no hamilton circuit, but the tour <s,0> → <s,1> → <s,0> of G has weight 0 ≤ 1 = k (paper.md slip 1)
--   - encoding: V a set of v nodes; N = V × {0,1} → V = Fin v (0-based); ⟨s,0⟩ = Fin.castAdd v s and ⟨s,1⟩ = Fin.natAdd v s in Fin (v + v); reason: Lean convention; the same instances up to relabelling
--   - encoding: a directed graph H = (V,E) → a Bool adjacency matrix adj on Fin v; a loop adj s s = true gives the arc (⟨s,0⟩,⟨s,0⟩) of weight 1; reason: Lean convention for a finite directed graph; for v ≥ 2 loops play no role on either side
--   - reading: a postman's tour is an "undirected (directed) cycle traversing each arc in R at least once" → a closed walk: a cyclic list of arc traversals in which nodes and arcs may repeat; the empty list is allowed; reason: the paper's own tour traverses each arc of R twice, so "cycle" means closed walk (paper.md reading 3); the empty tour matters only when R = ∅, where every reading gives weight 0
--   - encoding: a hamilton circuit: a directed cycle visiting each node exactly once → SchedComplexity.NoWait.HasHamiltonCircuit adj (vacuously true for v = 0); reason: for v ≥ 2 a cyclic ordering of all nodes with consecutive arcs is exactly such a cycle; at v = 0 both sides of the equivalence hold
-- source:
--   Lenstra, Rinnooy Kan, On general routing problems, Mathematisch Centrum report BW 42/74 (December 1974), p. 6, §2, proof of the Theorem, "The second reduction is similar. … H has a hamilton circuit if and only if G has a postman's tour of weight ≤ k. The proof is left to the reader."

import Mathlib
import Definitions.Def_RuralPostman_NPC_Reductions

namespace RuralPostman.NPC

theorem claim_directed {v : ℕ} (adj : Fin v → Fin v → Bool) (hv : v ≠ 1) :
    SchedComplexity.NoWait.HasHamiltonCircuit adj ↔ (drpOfGraph adj).RPYes true := by sorry

end RuralPostman.NPC
