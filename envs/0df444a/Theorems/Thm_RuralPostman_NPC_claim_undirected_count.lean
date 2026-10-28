-- Prove2me | Theorems.Thm_RuralPostman_NPC_claim_undirected_count
-- name    : RuralPostman.NPC.claim_undirected_count
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:38.728354+00:00
-- url     : https://prove2.me/theorems/400bdcce-27ea-4d8a-b929-c22987be21af
-- title:
--   §2, p. 6, proof of the Theorem — a postman's tour of G of weight ≤ k traverses k arcs of A−R exactly once
-- statement:
--   Let $H$ be an undirected graph on $V=\{0,\dots,v-1\}$ with $v\ge 3$, and let $G$ (arcs $A$, required arcs $R$, weight $w$, threshold $k=v$) be the rural postman instance of the undirected construction: a required pendant arc $(\langle s,0\rangle,\langle s,1\rangle)$ of weight $0$ for each vertex $s$, and an arc $(\langle s,0\rangle,\langle t,0\rangle)$ of weight $1$ for each edge $\{s,t\}$ of $H$.
--
--   Let $\tau$ be any undirected postman's tour of $G$ with weight at most $k$. Then $\tau$ traverses arcs of $A\setminus R$ exactly $k=v$ times in total, and no arc of $A\setminus R$ is traversed twice:
--   $$
--   \#\{i : \tau_i \notin R\} = v, \qquad \#\{i : \tau_i = a\}\le 1 \quad\text{for every } a\in A\setminus R .
--   $$
--   In other words, $\tau$ traverses $k$ arcs of $A\setminus R$ exactly once each.
--
--   This counting step is the core of the "only if" direction of the undirected equivalence.
--
--   **Formalization Note** Nodes are 0-based: $V$ is `Fin v`, and $N = V\times\{0,1\}$ is `Fin (v + v)` with $\langle s,0\rangle$ = `Fin.castAdd v s` and $\langle s,1\rangle$ = `Fin.natAdd v s`. A tour is a list of traversals (arc index, direction); `IsRequired e` says that arc $e$ lies in $R$, and `List.countP` counts traversals. $H$ is a symmetric Boolean adjacency matrix.
--
--   Differences from the source:
--   - encoding: V a set of v nodes; N = V × {0,1} → V = Fin v (0-based); ⟨s,0⟩ = Fin.castAdd v s and ⟨s,1⟩ = Fin.natAdd v s in Fin (v + v); reason: Lean convention; the same instances up to relabelling
--   - encoding: an undirected graph H = (V,E) → a Bool adjacency matrix adj on Fin v with IsSymm adj (diagonal ignored); reason: Lean convention for a finite undirected graph; loops play no role in a hamilton circuit on ≥ 3 nodes
--   - encoding: {(<s,0>,<t,0>) | (s,t) ∈ E} → one arc (⟨s,0⟩,⟨t,0⟩) of weight 1 for each pair s < t with adj s t = true; reason: each undirected edge of H gives one arc of G (paper.md reading 6)
--   - reading: a postman's tour is an "undirected (directed) cycle traversing each arc in R at least once" → a closed walk: a cyclic list of arc traversals in which nodes and arcs may repeat; the empty list is allowed; reason: the paper's own tour traverses each arc of R twice, so "cycle" means closed walk (paper.md reading 3); the empty tour matters only when R = ∅, where every reading gives weight 0
--   - reading: "such a tour traverses at most k times an arc from A-R. … it traverses k arcs from A-R exactly once" → the number of traversals of non-required arcs equals v (= k), and every non-required arc occurs in at most 1 traversal; reason: the conclusion "k arcs from A-R exactly once" in counting form; the intermediate bound "at most k" is implied
-- source:
--   Lenstra, Rinnooy Kan, On general routing problems, Mathematisch Centrum report BW 42/74 (December 1974), p. 6, §2, proof of the Theorem, "If G has a postman's tour of weight ≤ k, then …"

import Mathlib
import Definitions.Def_RuralPostman_NPC_Reductions

namespace RuralPostman.NPC

theorem claim_undirected_count {v : ℕ} (adj : Fin v → Fin v → Bool) (hs : IsSymm adj)
    (hv : 3 ≤ v) (τ : List (urpOfGraph adj).Traversal) (hτ : (urpOfGraph adj).IsTour false τ)
    (hw : (urpOfGraph adj).tourWeight τ ≤ (urpOfGraph adj).k) :
    τ.countP (fun t => ¬ (urpOfGraph adj).IsRequired t.1) = v ∧
      ∀ e, ¬ (urpOfGraph adj).IsRequired e → τ.countP (fun t => t.1 = e) ≤ 1 := by sorry

end RuralPostman.NPC
