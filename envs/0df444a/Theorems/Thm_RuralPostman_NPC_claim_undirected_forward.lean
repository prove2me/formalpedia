-- Prove2me | Theorems.Thm_RuralPostman_NPC_claim_undirected_forward
-- name    : RuralPostman.NPC.claim_undirected_forward
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:27.863256+00:00
-- url     : https://prove2.me/theorems/61cba6d4-d887-4e76-8b4a-a59d812c6dd1
-- title:
--   §2, p. 6, proof of the Theorem — a hamilton circuit of H gives a postman's tour of G traversing R twice and v arcs of A−R once, of weight v = k
-- statement:
--   Let $H$ be an undirected graph on $V=\{0,\dots,v-1\}$ with $v\ge 3$, and let $G$ (arcs $A$, required arcs $R$, weight $w$, threshold $k=v$) be the rural postman instance of the undirected construction: a required pendant arc $(\langle s,0\rangle,\langle s,1\rangle)$ of weight $0$ for each vertex $s$, and an arc $(\langle s,0\rangle,\langle t,0\rangle)$ of weight $1$ for each edge $\{s,t\}$ of $H$.
--
--   If $H$ has a hamilton circuit, then $G$ has an undirected postman's tour that
--
--   1. traverses every arc of $R$ exactly twice;
--   2. traverses exactly $v$ arcs of $A\setminus R$, each exactly once, and no other arc of $A\setminus R$;
--   3. has total weight
--   $$
--   \sum_{i} w(\tau_i) \;=\; v \;=\; k .
--   $$
--
--   This is the "if" direction of the equivalence on which the undirected reduction rests.
--
--   **Formalization Note** Nodes are 0-based: $V$ is `Fin v`, and $N = V\times\{0,1\}$ is `Fin (v + v)` with $\langle s,0\rangle$ = `Fin.castAdd v s` and $\langle s,1\rangle$ = `Fin.natAdd v s`. A tour is a list of traversals (arc index, direction); `IsRequired e` says that arc $e$ lies in $R$, and `List.countP` counts traversals. $H$ is a symmetric Boolean adjacency matrix. Clause 2 is stated as: the number of traversals of arcs outside $R$ is $v$, and each arc outside $R$ is traversed at most once.
--
--   Differences from the source:
--   - encoding: V a set of v nodes; N = V × {0,1} → V = Fin v (0-based); ⟨s,0⟩ = Fin.castAdd v s and ⟨s,1⟩ = Fin.natAdd v s in Fin (v + v); reason: Lean convention; the same instances up to relabelling
--   - encoding: an undirected graph H = (V,E) → a Bool adjacency matrix adj on Fin v with IsSymm adj (diagonal ignored); reason: Lean convention for a finite undirected graph; loops play no role in a hamilton circuit on ≥ 3 nodes
--   - encoding: {(<s,0>,<t,0>) | (s,t) ∈ E} → one arc (⟨s,0⟩,⟨t,0⟩) of weight 1 for each pair s < t with adj s t = true; reason: each undirected edge of H gives one arc of G (paper.md reading 6)
--   - reading: a postman's tour is an "undirected (directed) cycle traversing each arc in R at least once" → a closed walk: a cyclic list of arc traversals in which nodes and arcs may repeat; the empty list is allowed; reason: the paper's own tour traverses each arc of R twice, so "cycle" means closed walk (paper.md reading 3); the empty tour matters only when R = ∅, where every reading gives weight 0
--   - encoding: a hamilton circuit: a cycle visiting each node exactly once → SchedComplexity.NoWait.HasHamiltonCircuit adj: a bijection σ of Fin v with adj (σ i) (σ (i+1 mod v)) = true for all i; reason: for v ≥ 2 a cyclic ordering of all nodes with consecutive arcs is exactly such a cycle
--   - encoding: "traversing all arcs in R exactly twice and v arcs in A-R exactly once" → every required arc occurs in exactly 2 traversals; exactly v traversals are of non-required arcs; every non-required arc occurs in at most 1 traversal; reason: the same condition expressed by counting traversals
-- source:
--   Lenstra, Rinnooy Kan, On general routing problems, Mathematisch Centrum report BW 42/74 (December 1974), p. 6, §2, proof of the Theorem, "If H has a hamilton circuit, then G has a postman's tour …"

import Mathlib
import Definitions.Def_RuralPostman_NPC_Reductions

namespace RuralPostman.NPC

theorem claim_undirected_forward {v : ℕ} (adj : Fin v → Fin v → Bool) (hs : IsSymm adj)
    (hv : 3 ≤ v) (hH : SchedComplexity.NoWait.HasHamiltonCircuit adj) :
    ∃ τ : List (urpOfGraph adj).Traversal, (urpOfGraph adj).IsTour false τ ∧
      (∀ e, (urpOfGraph adj).IsRequired e → τ.countP (fun t => t.1 = e) = 2) ∧
      τ.countP (fun t => ¬ (urpOfGraph adj).IsRequired t.1) = v ∧
      (∀ e, ¬ (urpOfGraph adj).IsRequired e → τ.countP (fun t => t.1 = e) ≤ 1) ∧
      (urpOfGraph adj).tourWeight τ = v := by sorry

end RuralPostman.NPC
