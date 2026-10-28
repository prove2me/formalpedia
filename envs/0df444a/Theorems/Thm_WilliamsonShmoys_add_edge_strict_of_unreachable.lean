-- Prove2me | Theorems.Thm_WilliamsonShmoys_add_edge_strict_of_unreachable
-- name    : WilliamsonShmoys.add_edge_strict_of_unreachable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:28:51.915636+00:00
-- url     : https://prove2.me/theorems/f5e9abb1-4993-4ec0-a89b-c3a3251130a1
-- title:
--   Adding an edge between unreachable vertices is strict
-- statement:
--   If `u < v` and `u` cannot reach `v` in `G`, adjoining their edge produces a strict supergraph. A one-step path from adjacency contradicts unreachability, while the relation used by `fromRel` contributes the edge to the supremum.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.add_edge_strict_of_unreachable
    {V : Type} [LinearOrder V]
    (G : SimpleGraph V)
    {u v : V}
    (huv : u < v)
    (hUnreachable : ¬ G.Reachable u v) :
    G < G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v) := by sorry
