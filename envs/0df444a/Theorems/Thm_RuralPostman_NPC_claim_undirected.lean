-- Prove2me | Theorems.Thm_RuralPostman_NPC_claim_undirected
-- name    : RuralPostman.NPC.claim_undirected
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:07.041763+00:00
-- url     : https://prove2.me/theorems/88c1e681-8a35-4687-be86-59b73756bafd
-- title:
--   §2, p. 6, proof of the Theorem — H has a hamilton circuit iff G has a postman's tour of weight ≤ k (undirected, v ≥ 3)
-- statement:
--   Let $H$ be an undirected graph on $V=\{0,\dots,v-1\}$ with $v\ge 3$, and let $G$ (arcs $A$, required arcs $R$, weight $w$, threshold $k=v$) be the rural postman instance of the undirected construction: a required pendant arc $(\langle s,0\rangle,\langle s,1\rangle)$ of weight $0$ for each vertex $s$, and an arc $(\langle s,0\rangle,\langle t,0\rangle)$ of weight $1$ for each edge $\{s,t\}$ of $H$.
--
--   Then
--   $$
--   H \text{ has a hamilton circuit} \iff G \text{ has an undirected postman's tour of weight} \le k .
--   $$
--
--   Together with the polynomial size of $G$, this equivalence is what makes the construction a reduction from UNDIRECTED HAMILTON CIRCUIT to UNDIRECTED RURAL POSTMAN.
--
--   **Formalization Note** Nodes are 0-based: $V$ is `Fin v`, and $N = V\times\{0,1\}$ is `Fin (v + v)` with $\langle s,0\rangle$ = `Fin.castAdd v s` and $\langle s,1\rangle$ = `Fin.natAdd v s`. A tour is a list of traversals (arc index, direction); `IsRequired e` says that arc $e$ lies in $R$, and `List.countP` counts traversals. $H$ is a symmetric Boolean adjacency matrix.
--
--   Differences from the source:
--   - encoding: V a set of v nodes; N = V × {0,1} → V = Fin v (0-based); ⟨s,0⟩ = Fin.castAdd v s and ⟨s,1⟩ = Fin.natAdd v s in Fin (v + v); reason: Lean convention; the same instances up to relabelling
--   - encoding: an undirected graph H = (V,E) → a Bool adjacency matrix adj on Fin v with IsSymm adj (diagonal ignored); reason: Lean convention for a finite undirected graph; loops play no role in a hamilton circuit on ≥ 3 nodes
--   - encoding: {(<s,0>,<t,0>) | (s,t) ∈ E} → one arc (⟨s,0⟩,⟨t,0⟩) of weight 1 for each pair s < t with adj s t = true; reason: each undirected edge of H gives one arc of G (paper.md reading 6)
--   - reading: a postman's tour is an "undirected (directed) cycle traversing each arc in R at least once" → a closed walk: a cyclic list of arc traversals in which nodes and arcs may repeat; the empty list is allowed; reason: the paper's own tour traverses each arc of R twice, so "cycle" means closed walk (paper.md reading 3); the empty tour matters only when R = ∅, where every reading gives weight 0
--   - encoding: a hamilton circuit: a cycle visiting each node exactly once → SchedComplexity.NoWait.HasHamiltonCircuit adj: a bijection σ of Fin v with adj (σ i) (σ (i+1 mod v)) = true for all i; reason: for v ≥ 2 a cyclic ordering of all nodes with consecutive arcs is exactly such a cycle
-- source:
--   Lenstra, Rinnooy Kan, On general routing problems, Mathematisch Centrum report BW 42/74 (December 1974), p. 6, §2, proof of the Theorem, "We claim that H has a hamilton circuit if and only if G has a postman's tour of weight ≤ k."

import Mathlib
import Definitions.Def_RuralPostman_NPC_Reductions

namespace RuralPostman.NPC

theorem claim_undirected {v : ℕ} (adj : Fin v → Fin v → Bool) (hs : IsSymm adj) (hv : 3 ≤ v) :
    SchedComplexity.NoWait.HasHamiltonCircuit adj ↔ (urpOfGraph adj).RPYes false := by sorry

end RuralPostman.NPC
