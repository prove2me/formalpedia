-- Prove2me | Theorems.Thm_WilliamsonShmoys_coherent_shortest_root_paths
-- name    : WilliamsonShmoys.coherent_shortest_root_paths
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T21:43:57.274624+00:00
-- url     : https://prove2.me/theorems/f121bfb7-fabd-4c1f-921c-bc0acd2ce103
-- title:
--   Coherent shortest paths in a finite rooted graph
-- statement:
--   Every finite rooted graph admits shortest simple paths to all reachable vertices, chosen coherently: the chosen path to a vertex occurring on another chosen path is a subwalk of that path. Prove this by choosing distance-decreasing predecessors and recursing on distance. This isolates the BFS construction independently of planar geometry.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

theorem WilliamsonShmoys.coherent_shortest_root_paths
    {V : Type} [Finite V] (G : SimpleGraph V) (root : V) :
    ∃ P : (v : {x : V // G.Reachable root x}) → G.Walk root v.val,
      (∀ v, (P v).IsPath ∧ (P v).length = G.dist root v.val) ∧
      (∀ u v : {x : V // G.Reachable root x},
        u.val ∈ (P v).support → (P u).IsSubwalk (P v)) := by sorry
