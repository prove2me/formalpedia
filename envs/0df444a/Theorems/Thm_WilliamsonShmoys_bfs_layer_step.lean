-- Prove2me | Theorems.Thm_WilliamsonShmoys_bfs_layer_step
-- name    : WilliamsonShmoys.bfs_layer_step
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T16:02:39.916809+00:00
-- url     : https://prove2.me/theorems/a5c55481-4661-4c11-acb1-34bcbafbbcd2
-- title:
--   Layer recurrence for breadth-first search
-- statement:
--   Let $G$ be a simple graph, $r,w$ vertices and $t\in\mathbb N$. Suppose $w$ is not reachable from $r$ within distance $t$, that is, not ($w$ reachable from $r$ and $\operatorname{dist}(r,w)\le t$). Then
--
--   $$\bigl(w\text{ reachable from }r\ \wedge\ \operatorname{dist}(r,w)=t+1\bigr)\iff\exists u:\ u\text{ reachable from }r,\ \operatorname{dist}(r,u)=t,\ u\sim w.$$
--
--   This is the recurrence behind layer-by-layer breadth-first search: the vertices at distance exactly $t+1$ are the vertices not yet reached that have a neighbour at distance $t$. It is the correctness core of an $O(n^2)$ RAM computation of Baker's BFS levels, which scans the adjacency row of each vertex once.
--
--   **Formalization Note.** $\operatorname{dist}$ is `SimpleGraph.dist`, which is $0$ for unreachable pairs; reachability is stated explicitly for that reason.
-- source:
--   Standard BFS layering; used for the RAM computation of Baker levels in Williamson–Shmoys, Sect. 10.2, p. 270

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.bfs_layer_step {V : Type} (G : SimpleGraph V) (r w : V) (t : ℕ)
    (hw : ¬ (G.Reachable r w ∧ G.dist r w ≤ t)) :
    (G.Reachable r w ∧ G.dist r w = t + 1) ↔
      ∃ u, G.Reachable r u ∧ G.dist r u = t ∧ G.Adj u w := by sorry
